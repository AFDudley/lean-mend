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
  | .deleteTactic => some ""
  | .rename _ _ | .heartbeats _ => none

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
    | op, some d, some .body => do
      let n ← pickNode r.family nodes
      let repl ← applyOp op n
      pure (mk (.body d) n.start n.stop repl)
    | _, _, _ => none

/-- All candidates for a site, in entrenchment order (concept C3): the derived
alias candidates, then ratified rules, then proposed rules, each in rule-list
order. A candidate that an earlier one already proposed is dropped. -/
def proposeAll (m : AliasMap) (rules : List Rule) (nodes : List Node) (s : Site) :
    List Candidate :=
  let byE (e : Entrenchment) := (rules.filter (·.entrenchment == e)).flatMap
    (ruleCandidates · nodes s)
  let all := propose m s ++ byE .ratified ++ byE .proposed
  all.foldl (fun acc c =>
    if acc.any fun d => d.start == c.start && d.stop == c.stop && d.replacement == c.replacement
    then acc else acc ++ [c]) []

end LeanMend
