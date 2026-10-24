import LeanMend.Core.Propose

/-!
# Edit operations

Pure functions from a rule, the syntax nodes that contain a site (innermost
first, from the probe's `node`), and the site, to candidates. See
`docs/rules.md` § Edit operations. An operation that does not apply to the node
gives no candidate.

Every candidate except `rename` and `heartbeats` edits one tactic node inside a
body region. A site in a statement region gets no candidate from an operation:
`EditTarget` has no constructor for a statement (decision D5).
-/

namespace LeanMend

/-- The first-token keywords of each tactic family. -/
def TacticFamily.keywords : TacticFamily → List String
  | .simp => ["simp", "simp?", "simpa", "simpa?", "dsimp", "simp_all", "simp_arith"]
  | .rw => ["rw", "rewrite", "erw", "rwa"]
  | .exact => ["exact"]
  | .decide => ["decide"]
  | .any => []

/-- A node that holds a sequence of tactics, not one tactic. Its first token is
the first tactic's keyword, so it must not match a family. -/
def Node.isSequence (n : Node) : Bool :=
  n.kind == "null" || n.kind.endsWith "tacticSeq" || n.kind.endsWith "tacticSeq1Indented" ||
    n.kind.endsWith "tacticSeqBracketed" || n.kind.endsWith "seq1"

/-- The first node of the family: a single tactic whose first token is one of
the family's keywords. `any` takes the first single tactic. `nodes` lists the
nodes at the site's start, innermost first, then those at its end. -/
def pickNode (f : TacticFamily) (nodes : List Node) : Option Node :=
  nodes.find? fun n =>
    !n.isSequence &&
    match n.tokens with
    | t :: _ => f == .any || f.keywords.contains t.text
    | [] => false

/-- Bytes of `s` before and after the byte range `[a, b)`, relative to `s`. -/
private def splice (s : String) (a b : Nat) (ins : String) : String :=
  let bs := s.toUTF8
  String.fromUTF8! (bs.extract 0 a) ++ ins ++ String.fromUTF8! (bs.extract b bs.size)

/-- The replacement text for node `n` under `op`, or `none` if `op` does not
apply. Token ranges are absolute; `n.start` converts them to node offsets. -/
def applyOp (op : EditOp) (n : Node) : Option String :=
  let rel (t : Token) := (t.start - n.start, t.stop - n.start)
  match op with
  | .simpArgAdd l =>
    if n.tokens.any (·.text == l) then none else
    match n.tokens.findIdx? (·.text == "[") with
    | some i =>
      -- the matching `]`: depth count from the first `[`
      let rest := n.tokens.drop (i + 1)
      let close := rest.foldl (init := ((1 : Nat), (none : Option Token)))
        fun (d, found) t => match found with
          | some _ => (d, found)
          | none =>
            if t.text == "[" then (d + 1, none)
            else if t.text == "]" then (if d == 1 then (0, some t) else (d - 1, none))
            else (d, none)
      match close.2 with
      | some c =>
        let empty := (rest.head?.map (·.text == "]")).getD false
        some (splice n.text (rel c).1 (rel c).1 (if empty then l else s!", {l}"))
      | none => none
    | none =>
      -- no list: insert ` [l]` after the keyword (and after `only`)
      match n.tokens with
      | k :: o :: _ =>
        let after := if o.text == "only" then o else k
        some (splice n.text (rel after).2 (rel after).2 s!" [{l}]")
      | [k] => some (splice n.text (rel k).2 (rel k).2 s!" [{l}]")
      | [] => none
  | .simpaToExact =>
    match n.tokens with
    | k :: _ =>
      if k.text != "simpa" then none else
      match n.tokens.find? (·.text == "using") with
      | some u =>
        let term := String.fromUTF8! (n.text.toUTF8.extract (rel u).2 n.text.utf8ByteSize)
        some s!"exact {term.trimAscii.toString}"
      | none => none
    | [] => none
  | .keywordSwap a b =>
    match n.tokens with
    | k :: _ => if k.text == a then some (splice n.text (rel k).1 (rel k).2 b) else none
    | [] => none
  | .matchToIf =>
    -- exactly `match d with | p => a | _ => b`, tokens at the top of the node
    let slice (a b : Nat) := (String.fromUTF8! (n.text.toUTF8.extract (a - n.start) (b - n.start))).trimAscii.toString
    let bars := n.tokens.filter (·.text == "|")
    let arrows := n.tokens.filter (·.text == "=>")
    match n.tokens.head?, n.tokens.find? (·.text == "with"), bars, arrows with
    | some m, some w, [b1, b2], [a1, a2] =>
      if m.text != "match" then none else
      let d := slice m.stop w.start
      let p := slice b1.stop a1.start
      let r1 := slice a1.stop b2.start
      let p2 := slice b2.stop a2.start
      let r2 := slice a2.stop n.stop
      -- the first pattern must bind nothing: no identifier that starts lower case
      let binds := (runs p).any fun w => (w.toList.headD 'A').isLower
      if p2 != "_" || binds || p.isEmpty then none
      else some s!"if {d} = {p} then {r1}\n{String.ofList (List.replicate n.column ' ')}else {r2}"
    | _, _, _, _ => none
  | .matchOnVal =>
    let bars := n.tokens.filter (·.text == "|")
    let arrows := n.tokens.filter (·.text == "=>")
    match n.tokens.head?, n.tokens.find? (·.text == "with") with
    | some m, some w =>
      if m.text != "match" || bars.isEmpty || bars.length != arrows.length then none else
      let pats := (bars.zip arrows).map fun (b, a) =>
        (String.fromUTF8! (n.text.toUTF8.extract (b.stop - n.start) (a.start - n.start))).trimAscii.toString
      let numeral (p : String) := p == "_" || (!p.isEmpty && p.all Char.isDigit)
      if !pats.all numeral then none else
      let d := (String.fromUTF8! (n.text.toUTF8.extract (m.stop - n.start) (w.start - n.start))).trimAscii.toString
      let d' := if d.all identChar then s!"{d}.val" else s!"({d}).val"
      let bs := n.text.toUTF8
      some (String.fromUTF8! (bs.extract 0 (m.stop - n.start)) ++ " " ++ d' ++ " " ++
            String.fromUTF8! (bs.extract (w.start - n.start) bs.size))
    | _, _ => none
  | .deleteTactic => some ""
  | .appendTactic t =>
    some (n.text ++ "\n" ++ String.ofList (List.replicate n.column ' ') ++ t)
  | .rename _ _ | .renamePrefix _ _ | .replaceInBody _ _ _ | .heartbeats _ => none

/-- The identifier runs of a replacement, for the structural check
(`Candidate.clean`). -/
def replacementTokens (r : String) : List String :=
  (runs r).filter fun w => (w.toList.headD ' ').isAlpha || w.startsWith "_"

/-- Candidates from one rule for one site. -/
def ruleCandidates (r : Rule) (nodes : List Node) (s : Site) : List Candidate :=
  if classify s.diagnostic != r.cls then [] else
  r.ops.filterMap fun op =>
    let mk (target : EditTarget) (a b : Nat) (repl : String) : Candidate :=
      { rule := s!"{r.name}: {repr op}", entrenchment := r.entrenchment, target,
        start := a, stop := b, replacement := repl, tokens := replacementTokens repl }
    match op, s.decl, s.region with
    | .heartbeats n, some d, _ =>
      s.declStart.map fun p => mk (.beforeDecl d) p p s!"set_option maxHeartbeats {n} in\n"
    | .rename a b, _, _ =>
      if identOf s.diagnostic == some a then some (mk (.aliasRename a b) s.start s.stop b) else none
    | .replaceInBody d old new, some sd, _ => do
      guard (d == sd)
      let (bodyStart, bodyText) ← s.body
      -- exactly one occurrence, at a known byte offset
      match bodyText.splitOn old with
      | [before, _] =>
        let a := bodyStart + before.utf8ByteSize
        pure (mk (.body d) a (a + old.utf8ByteSize) new)
      | _ => none
    | .renamePrefix a b, _, _ =>
      match swapPrefix a b s.text with
      | some t => some (mk (.aliasRename a b) s.start s.stop t)
      | none =>
        -- `open X (n …)`: Lean reports `X.n` at the token `n`; the namespace
        -- token `X` is the one that moves.
        let ns (x : String) := ".".intercalate ((x.splitOn ".").dropLast)
        if (identOf s.diagnostic).any (fun i => (swapPrefix a b i).isSome) then do
          let n ← nodes.find? (·.kind.endsWith "Command.open")
          let t ← n.tokens.find? (·.text == ns a)
          pure (mk (.aliasRename a b) t.start t.stop (ns b))
        else none
    | op, some d, some .body => do
      let n ← pickNode r.family nodes
      let repl ← applyOp op n
      pure (mk (.body d) n.start n.stop repl)
    | _, _, _ => none

/-- One binder group's content: names and spaces only, at least one name. -/
private def namesOnly (c : String) : Bool :=
  c.any (· != ' ') && c.all fun ch => ch == ' ' || identChar ch

/-- Every binder group `{a b}`, `(a b)` or `⦃a b⦄` whose content is names and
spaces only becomes `{a b : _}`, Lean's own hint for `binderOverride`. Groups
with a type, a `:=`, a `|` or any other symbol are kept. `none` if nothing
changes. Lean reports only the first offending group, and the type fails until
every group is fixed, so all groups change in one edit. -/
def annotateBinders (t : String) : Option String :=
  let pairs := [('{', '}'), ('(', ')'), ('⦃', '⦄')]
  -- one pass: copy text; at an opening bracket, look for its close on the
  -- same group with only names and spaces between
  let rec go (cs : List Char) (acc : List Char) (changed : Bool) : List Char × Bool :=
    match cs with
    | [] => (acc.reverse, changed)
    | c :: rest =>
      match pairs.lookup c with
      | some close =>
        let inner := rest.takeWhile (· != close)
        let after := rest.drop inner.length
        if after.head? == some close && namesOnly (String.ofList inner) then
          let grp := [c] ++ inner ++ " : _".toList ++ [close]
          go (after.drop 1) (grp.reverse ++ acc) true
        else go rest (c :: acc) changed
      | none => go rest (c :: acc) changed
  termination_by cs.length
  decreasing_by all_goals simp_wf; all_goals omega
  match go t.toList [] false with
  | (out, true) => some (String.ofList out)
  | (_, false) => none

/-- The identifier runs of `new` that `old` does not have, counted with
multiplicity: what an edit adds. -/
def addedTokens (old new : String) : List String :=
  (replacementTokens new).foldl (init := ([], replacementTokens old)) (fun (acc, rest) t =>
    if rest.contains t then (acc, rest.erase t) else (acc ++ [t], rest)) |>.1

/-- The built-in type-narrowing candidate (decision D11): a statement edit of
the whole type declaration, so the shell applies it only with
`--annotate-binders`. -/
def typeCandidates (s : Site) : List Candidate :=
  match classify s.diagnostic, s.decl, s.statement with
  | .binderOverride, some d, some (a, txt) =>
    match annotateBinders txt with
    | some r =>
      [{ rule := "annotate-binders (Lean's hint)", entrenchment := .derived,
         target := .typeAnnotation d, start := a, stop := a + txt.utf8ByteSize,
         -- the clean check sees what the edit adds: the type keeps its own
         -- `inductive`/`structure`/`class` keyword, which D10 must not count
         replacement := r, tokens := addedTokens txt r }]
    | none => []
  | _, _, _ => []

/-- All candidates for a site, in entrenchment order (concept C3): the derived
alias candidates, then ratified rules, then proposed rules, each in rule-list
order. A candidate that an earlier one already proposed is dropped. -/
def proposeAll (m : AliasMap) (rules : List Rule) (nodes : List Node)
    (annotate : Bool) (s : Site) : List Candidate :=
  let byE (e : Entrenchment) := (rules.filter (·.entrenchment == e)).flatMap
    (ruleCandidates · nodes s)
  let all := propose m s ++ (if annotate then typeCandidates s else []) ++
    byE .ratified ++ byE .proposed
  all.foldl (fun acc c =>
    if acc.any fun d => d.start == c.start && d.stop == c.stop && d.replacement == c.replacement
    then acc else acc ++ [c]) []

/-- The namespace moves that the rules declare (`renamePrefix`). -/
def Rule.prefixPairs (rs : List Rule) : List (String × String) :=
  rs.flatMap fun r => r.ops.filterMap fun
    | .renamePrefix a b => some (a, b)
    | _ => none

end LeanMend
