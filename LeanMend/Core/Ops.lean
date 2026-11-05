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
  | .simpaSplit =>
    let pad := String.ofList (List.replicate n.column ' ')
    match n.tokens with
    | k :: _ =>
      if k.text != "simpa" then none else
      match n.tokens.dropWhile (·.text != "using") with
      | u :: rest@(_ :: _) =>
        let before := String.fromUTF8! (n.text.toUTF8.extract (k.stop - n.start) (u.start - n.start))
        let simpPart := s!"simp{before.trimAsciiEnd.toString}"
        let term := String.fromUTF8! (n.text.toUTF8.extract (u.stop - n.start) n.text.utf8ByteSize)
        -- a term: name it first. A `have` inside a proof is not a
        -- declaration (decision D10).
        let named := s!"have := {term.trimAscii.toString}\n{pad}{simpPart} at this ⊢\n{pad}exact this"
        match rest with
        | [h] =>
          if !(h.text.all identChar) then none
          -- A dotted name (`hwf.d3`, a field of a hypothesis) is a term, not
          -- a hypothesis: Lean refuses it after `at` ("expected single
          -- reference to variable"). EquiVM `Reasoning.SolcRoutines` 1464.
          else if h.text.contains '.' then some named
          -- a hypothesis name: simplify it in place
          else some s!"{simpPart} at {h.text} ⊢\n{pad}exact {h.text}"
        | _ => some named
      | _ => none
    | [] => none
  | .simpaUsingBang =>
    -- `using` becomes `using!`: the close at default transparency (Lean
    -- v4.33 `simpa using!`). `simpa … using! T` has the token `using!`, so
    -- it gives no candidate.
    match n.tokens with
    | k :: _ =>
      if k.text != "simpa" then none else
      match n.tokens.find? (·.text == "using") with
      | some u => some (splice n.text (rel u).1 (rel u).2 "using!")
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
  | .rename _ _ | .renamePrefix _ _ | .replaceInBody _ _ _ | .heartbeats _ | .valCompare
  | .closeBullet _ | .simpArgAddPrior _ => none

/-- The simp-family tactic that comes last before the site's own tactic, in
the innermost indented tactic sequence that holds byte `site`, as a node of
its own. A tactic of that sequence starts a line at the sequence's column; the
site's own tactic is the last one that starts at or before `site`. The node
ends where the next tactic starts, without the trailing white space. `none`
if no simp-family tactic comes before the site's tactic in that sequence. -/
def priorSimp (nodes : List Node) (site : Nat) : Option Node := do
  let q ← nodes.find? (·.kind.endsWith "tacticSeq1Indented")
  let bs := q.text.toUTF8
  let between (a b : Nat) := String.fromUTF8! (bs.extract (a - q.start) (b - q.start))
  -- only `q.column` spaces precede the token on its line
  let heads := q.tokens.filter fun t =>
    t.start == q.start ||
      match (between q.start t.start).splitOn "\n" with
      | _ :: rest@(_ :: _) =>
        let l := rest.getLast!
        l.length == q.column && l.all (· == ' ')
      | _ => false
  let own ← (heads.filter (·.start ≤ site)).getLast?
  let prior ← (heads.filter (·.start < own.start)).reverse.find?
    (TacticFamily.simp.keywords.contains ·.text)
  let next ← heads.find? (·.start > prior.start)
  let text := (between prior.start next.start).trimAsciiEnd.toString
  let stop := prior.start + text.utf8ByteSize
  pure { kind := "priorSimp", start := prior.start, stop, text, column := q.column,
         tokens := q.tokens.filter fun t => prior.start ≤ t.start && t.stop ≤ stop }

/-- The variable in Lean's message `Decidable (x✝ = n)`: `x`. -/
def decidableVar (d : Diagnostic) : Option String :=
  match d.text.splitOn "Decidable (" with
  | _ :: rest :: _ =>
    match rest.splitOn " = " with
    | v :: _ :: _ =>
      let v := (String.ofList (v.toList.filter (· != '✝'))).trimAscii.toString
      if !v.isEmpty && v.all identChar then some v else none
    | _ => none
  | _ => none

/-- `x` becomes `x.val` where `x` is matched (`match x with`) or compared with
a numeral (`x = n`, `x ≠ n`), everywhere in `src`. Returns the new text and the
byte spans of the rewritten names in it, or `none` if nothing changes. -/
def valOfLiterals (x src : String) : Option (String × List (Nat × Nat)) :=
  let rs := (runs src).toArray
  let blank (r : String) := r.all Char.isWhitespace
  let nextTok (i : Nat) : Option Nat :=
    (List.range (rs.size - (i + 1))).findSome? fun k => if blank rs[i + 1 + k]! then none else some (i + 1 + k)
  let prevTok (i : Nat) : Option Nat :=
    (List.range i).findSome? fun k => if blank rs[i - 1 - k]! then none else some (i - 1 - k)
  let numeral (j : Nat) := let t := rs[j]!; !t.isEmpty && t.all Char.isDigit
  let hit (i : Nat) : Bool :=
    rs[i]! == x &&
    (((prevTok i).any (rs[·]! == "match") && (nextTok i).any (rs[·]! == "with")) ||
     (match nextTok i with
      | some j => let op := rs[j]!.trimAscii.toString
                  (op == "=" || op == "≠") && (nextTok j).any numeral
      | none => false))
  let (out, spans, _, n) := (List.range rs.size).foldl (init := ("", ([] : List (Nat × Nat)), 0, 0))
    fun (out, spans, pos, n) i =>
      let r := rs[i]!
      if hit i then
        let r' := r ++ ".val"
        (out ++ r', spans ++ [(pos, pos + r'.utf8ByteSize)], pos + r'.utf8ByteSize, n + 1)
      else (out ++ r, spans, pos + r.utf8ByteSize, n)
  if n == 0 then none else some (out, spans)

/-- The `valCompare` edit for a site: the whole declaration, rewritten. -/
def valCompareEdit (s : Site) : Option (Nat × String × String × List (Nat × Nat)) := do
  let x ← decidableVar s.diagnostic
  let (a, txt) ← s.declText
  let (t, spans) ← valOfLiterals x txt
  pure (a, txt, t, spans.map fun (p, q) => (a + p, a + q))

/-- Whether the `valCompare` edit changes the declaration's statement. -/
def valCompareTouchesStatement (s : Site) : Bool :=
  match decidableVar s.diagnostic, s.statement with
  | some x, some (_, st) => (valOfLiterals x st).isSome
  | _, _ => false

/-- Every name between backticks in a diagnostic's text. -/
def namesIn (d : Diagnostic) : List String :=
  ((d.text.splitOn "`").zipIdx.filter (·.2 % 2 == 1)).map (·.1)

/-- Every identifier in `src` that starts with the name `a` gets `b` in its
place. Returns the new text and the byte spans of the renamed identifiers in
it, or `none` if nothing changes. -/
def renameAll (a b src : String) : Option (String × List (Nat × Nat)) :=
  let (out, spans, pos, n) := (runs src).foldl (init := ("", ([] : List (Nat × Nat)), 0, 0))
    fun (out, spans, pos, n) r =>
      match swapPrefix a b r with
      | some r' => (out ++ r', spans ++ [(pos, pos + r'.utf8ByteSize)], pos + r'.utf8ByteSize, n + 1)
      | none => (out ++ r, spans, pos + r.utf8ByteSize, n)
  let _ := pos
  if n == 0 then none else some (out, spans)

/-- The identifier runs of a replacement, for the structural check
(`Candidate.clean`). -/
def replacementTokens (r : String) : List String :=
  (runs r).filter fun w => (w.toList.headD ' ').isAlpha || w.startsWith "_"

/-- The identifier runs of `new` that `old` does not have, counted with
multiplicity: what an edit adds. -/
def addedTokens (old new : String) : List String :=
  (replacementTokens new).foldl (init := ([], replacementTokens old)) (fun (acc, rest) t =>
    if rest.contains t then (acc, rest.erase t) else (acc ++ [t], rest)) |>.1

/-- Candidates from one rule for one site. `follow` is
`--follow-definition-changes` (decision D12, X7): it lets a `valCompare` edit
that also touches the declaration's statement go out as one candidate. -/
def ruleCandidates (follow : Bool) (r : Rule) (nodes : List Node) (s : Site) : List Candidate :=
  -- A namespace move answers any site whose message names a moved name,
  -- whatever its class ("Invalid pattern variable … `Batteries.RBNode.Stream.nil`").
  let moves := r.ops.any fun
    | .renamePrefix a b => (namesIn s.diagnostic).any fun n => (swapPrefix a b n).isSome
    | _ => false
  if classify s.diagnostic != r.cls && !moves then [] else
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
      -- A namespace move is all-or-nothing: rename every occurrence in the
      -- file in one edit, because renaming one site of a declaration lets Lean
      -- check the rest of it, which still has the old names.
      match renameAll a b s.file with
      | some (t, spans) =>
        some { mk (.aliasRename a b) 0 s.file.utf8ByteSize t with
               tokens := addedTokens s.file t, changed := spans }
      | none =>
        -- `open X (n …)`: Lean reports `X.n` at the token `n`; the namespace
        -- token `X` is the one that moves.
        let ns (x : String) := ".".intercalate ((x.splitOn ".").dropLast)
        if (identOf s.diagnostic).any (fun i => (swapPrefix a b i).isSome) then do
          let n ← nodes.find? (·.kind.endsWith "Command.open")
          let t ← n.tokens.find? (·.text == ns a)
          pure (mk (.aliasRename a b) t.start t.stop (ns b))
        else none
    | .closeBullet t, some d, some .body => do
      -- the innermost bullet that holds the site
      let n ← nodes.find? (·.kind == "Lean.cdot")
      pure (mk (.body d) n.start n.stop s!"· {t}")
    | .simpArgAddPrior l, some d, some .body => do
      -- the site's own tactic is of the rule's family; the edit is the simp before it
      let _ ← pickNode r.family nodes
      let n ← priorSimp nodes s.start
      let repl ← applyOp (.simpArgAdd l) n
      pure (mk (.body d) n.start n.stop repl)
    | .valCompare, some d, _ => do
      let (a, txt, t, spans) ← valCompareEdit s
      -- The pattern also occurs in `d`'s statement (X7): under
      -- --follow-definition-changes the body edit and its statement follow
      -- are one candidate, spanning the whole declaration, in one rebuild.
      -- Without the flag, no candidate goes out here; `followCandidates`
      -- gives the default run its warning.
      if valCompareTouchesStatement s then
        guard follow
        pure { rule := s!"{r.name}: {repr op} (following a definition change)",
               entrenchment := r.entrenchment, target := .followStatement d,
               start := a, stop := a + txt.utf8ByteSize, replacement := t,
               tokens := addedTokens txt t, changed := spans }
      else
        pure { mk (.body d) a (a + txt.utf8ByteSize) t with
               tokens := addedTokens txt t, changed := spans }
    | op, some d, some .body => do
      let n ← pickNode r.family nodes
      let repl ← applyOp op n
      pure (mk (.body d) n.start n.stop repl)
    | _, _, _ => none

/-- One binder group's content: names and spaces only, at least one name. -/
private def namesOnly (c : String) : Bool :=
  c.any (· != ' ') && c.all fun ch => ch == ' ' || identChar ch

/-- Every binder group `{a b}`, `(a b)` or `⦃a b⦄` in a constructor's binder
position whose content is names and spaces only becomes `{a b : _}`, Lean's own
hint for `binderOverride`. A binder position is between `| name` and the first
`:` outside brackets, which starts the constructor's type: a group in the type,
such as the application `(f a b)`, is never changed. `none` if nothing changes.
Lean reports only the first offending group, and the type fails until every
group is fixed, so all groups change in one edit. -/
def annotateBinders (t : String) : Option String :=
  let pairs := [('{', '}'), ('(', ')'), ('⦃', '⦄')]
  let closes := ['}', ')', '⦄', ']']
  let opens := ['{', '(', '⦃', '[']
  -- mode 0: outside binders; 1: after `|`, reading the name; 2: in binders
  let rec go (cs : List Char) (acc : List Char) (mode depth : Nat) (changed : Bool) :
      List Char × Bool :=
    match cs with
    | [] => (acc.reverse, changed)
    | c :: rest =>
      if c == '|' && depth == 0 then go rest (c :: acc) 1 0 changed
      else if mode == 1 then
        -- the name ends at the first space after it
        if c == ' ' && acc.head? != some '|' && acc.head? != some ' ' then go rest (c :: acc) 2 0 changed
        else go rest (c :: acc) 1 0 changed
      else if mode == 2 && c == ':' && depth == 0 then go rest (c :: acc) 0 0 changed
      else if mode == 2 && depth == 0 then
        match pairs.lookup c with
        | some close =>
          let inner := rest.takeWhile (· != close)
          let after := rest.drop inner.length
          if after.head? == some close && namesOnly (String.ofList inner) then
            go (after.drop 1) (([c] ++ inner ++ " : _".toList ++ [close]).reverse ++ acc) 2 0 true
          else go rest (c :: acc) 2 1 changed
        | none => go rest (c :: acc) 2 0 changed
      else if opens.contains c then go rest (c :: acc) mode (depth + 1) changed
      else if closes.contains c then go rest (c :: acc) mode (depth - 1) changed
      else go rest (c :: acc) mode depth changed
  termination_by cs.length
  decreasing_by all_goals simp_wf; all_goals omega
  match go t.toList [] 0 0 false with
  | (out, true) => some (String.ofList out)
  | (_, false) => none

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

/-- Statement candidates for decision D12: the `match` operations of `rules`
applied at a site in a statement. The shell passes only the rules that were
already accepted in a declaration body this run. -/
def followCandidates (rules : List Rule) (nodes : List Node) (s : Site) : List Candidate :=
  match s.decl, s.region with
  | some d, some .statement =>
    rules.flatMap fun r =>
      if classify s.diagnostic != r.cls then [] else
      r.ops.filterMap fun op =>
        if op == .valCompare then do
          guard (valCompareTouchesStatement s)
          let (a, txt, t, spans) ← valCompareEdit s
          pure { rule := s!"{r.name}: {repr op} (following a definition change)",
                 entrenchment := r.entrenchment, target := .followStatement d,
                 start := a, stop := a + txt.utf8ByteSize, replacement := t,
                 tokens := addedTokens txt t, changed := spans }
        else if !(op == .matchOnVal || op == .matchToIf) then none else do
        let n ← pickNode r.family nodes
        let repl ← applyOp op n
        pure { rule := s!"{r.name}: {repr op} (following a definition change)",
               entrenchment := r.entrenchment, target := .followStatement d,
               start := n.start, stop := n.stop, replacement := repl,
               tokens := addedTokens n.text repl }
  | _, _ => []

/-- All candidates for a site, in entrenchment order (concept C3): the derived
alias candidates, then ratified rules, then proposed rules, each in rule-list
order. A candidate that an earlier one already proposed is dropped. -/
def proposeAll (m : AliasMap) (rules : List Rule) (nodes : List Node)
    (annotate follow : Bool) (followed : List String) (s : Site) : List Candidate :=
  -- A rule that only closes bullets replaces the author's proof: the least
  -- preferred repair, so it runs after every other rule of its entrenchment.
  let closer (r : Rule) := r.ops.all fun | .closeBullet _ => true | _ => false
  let byE (e : Entrenchment) :=
    let rs := rules.filter (·.entrenchment == e)
    (rs.filter (!closer ·) ++ rs.filter closer).flatMap (ruleCandidates follow · nodes s)
  let all := propose m s ++ (if annotate then typeCandidates s else []) ++
    byE .ratified ++ byE .proposed ++
    followCandidates (rules.filter (followed.contains ·.name)) nodes s
  all.foldl (fun acc c =>
    if acc.any fun d => d.start == c.start && d.stop == c.stop && d.replacement == c.replacement
    then acc else acc ++ [c]) []

/-- The namespace moves that the rules declare (`renamePrefix`). -/
def Rule.prefixPairs (rs : List Rule) : List (String × String) :=
  rs.flatMap fun r => r.ops.filterMap fun
    | .renamePrefix a b => some (a, b)
    | _ => none

end LeanMend
