import LeanMend.Core.Ops
import LeanMend.Spec.Types
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# The cause of a finding

Pure functions that compute what a card explains (`docs/verification.md`
§ What a card explains). The shell gathers the data at each toolchain (the
probe's `explain` and `proofs`, the lake manifests, git), and this module
computes, with no IO:

* for a Violation finding, per changed axiom: the shortest dependency path at
  the toolchain that has the axiom, the cause (the constant nearest the axiom
  whose own axiom set differs between the toolchains), and the path to the
  cause at the other toolchain (`explainViolation`);
* the grouping of findings by cause (`groupCauses`);
* for a Behavior finding: the line diff of the body, and whether every changed
  byte lies inside a proof (`bodyChange`).
-/

namespace LeanMend

/-- One constant at one toolchain, as the probe's `explain` reports it. -/
structure Const where
  name : String
  module : String
  /-- The axioms of the constant, in the certificate's form (`Parse.axiomSet`). -/
  axioms : List String
  /-- The constants that `collectAxioms` visits next from this one (`axEdges`). -/
  uses : List String
  /-- For an axiom: its name in the certificate's form. -/
  axiomName : Option String
  /-- Whether the constant carries Lean's `@[congr]` attribute (the probe's
  `explain`, `docs/rules.md` § Axiom-finding rules, `causeTag`'s
  `congrLemma` case). -/
  congr : Bool := false
  deriving Repr, Inhabited, DecidableEq

/-- The package that owns a module at one toolchain, with its revision: the
`rev` of the target's `lake-manifest.json`, the toolchain for Lean core, or
the target's commit for the target's own modules. -/
structure Owner where
  package : String
  rev : String
  deriving Repr, DecidableEq

/-- The dependency data of one toolchain. -/
structure Side where
  toolchain : String
  /-- Every constant that the findings' declarations reach, and the closure
  of each name that the other toolchain's paths needed (`lookups`). -/
  consts : List Const
  /-- The owner of each module of `consts`. -/
  owners : List (String × Owner)
  /-- The names that the probe was asked for and that the environment of the
  findings' modules does not hold. -/
  missing : List String
  deriving Repr

/-- The constants of a side by name. -/
def Side.index (s : Side) : Std.HashMap String Const :=
  s.consts.foldl (fun m c => m.insert c.name c) {}

/-- How the names of one toolchain map to the other (the alias map and the
namespace moves, `docs/verification.md` § The certificate). -/
structure Names where
  toAfter : String → String
  /-- The names at the old toolchain that can have become `n`. -/
  toBase : String → List String

/-- The alias map as `Names`: `rename` forward, every old name of a pair
backward, then the name itself. -/
def Names.ofAliases (m : AliasMap) : Names where
  toAfter := m.rename
  toBase n := (m.pairs.filter (·.2 == n)).map (·.1) ++ [n]

/-- Whether an axiom is added at the new toolchain or removed. -/
inductive Change where
  | added
  | removed
  deriving DecidableEq, Repr

/-- A constant at one toolchain, as a card shows it. -/
inductive Presence where
  | present (name module : String) (owner : Option Owner) (axioms : List String)
  /-- The environment of the findings' modules holds no constant of the name. -/
  | absent (name : String)
  deriving DecidableEq, Repr

/-- One constant of a path: at the path's toolchain and at the other one. -/
structure Link where
  here : Presence
  there : Presence
  deriving DecidableEq, Repr

/-- `here` and `there` differ: one is absent, or the axiom sets differ. -/
def Link.differs (l : Link) : Bool :=
  match l.here, l.there with
  | .present _ _ _ a, .present _ _ _ b => a != b
  | _, _ => true

def Presence.name : Presence → String
  | .present n .. => n
  | .absent n => n

/-- The cause of one changed axiom of one declaration. -/
structure AxiomCause where
  axiom_ : String
  change : Change
  /-- The shortest path at the toolchain that has the axiom: the declaration
  first, the axiom last. -/
  path : List Link
  /-- The constant on `path` nearest the axiom whose own axiom set differs. -/
  cause : Link
  /-- The shortest path to the cause at the other toolchain, from the
  declaration, or why it is not computed. -/
  otherPath : Except String (List String)
  deriving Repr

/-- The explanation of one changed axiom: its cause, or why it is not computed. -/
inductive AxiomExplanation where
  | cause (c : AxiomCause)
  | notComputed (axiom_ : String) (change : Change) (reason : String)
  deriving Repr

/-- The shortest path in `idx` from `src` to a constant that satisfies
`goal`, by breadth-first search over `uses`, both ends included. Each
round takes one constant from the queue, and a constant enters the queue at
most once, so `idx.size + 1` rounds visit every constant. -/
def shortestPath (idx : Std.HashMap String Const) (src : String) (goal : Const → Bool) :
    Option (List String) := Id.run do
  let some s := idx[src]? | return none
  if goal s then return some [src]
  let mut parent : Std.HashMap String String := {}
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert src
  let mut queue : Array String := #[src]
  let mut i := 0
  let mut hit : Option String := none
  for _ in [0:idx.size + 1] do
    if hit.isSome then break
    let some n := queue[i]? | break
    i := i + 1
    let some c := idx[n]? | continue
    for u in c.uses do
      if hit.isNone && !seen.contains u then
        seen := seen.insert u
        parent := parent.insert u n
        if let some cu := idx[u]? then
          if goal cu then hit := some u
          queue := queue.push u
  let some t := hit | return none
  -- Walk the parents back to `src`: at most one step per constant seen.
  let mut path := [t]
  let mut cur := t
  for _ in [0:seen.size] do
    if cur == src then break
    let some p := parent[cur]? | break
    path := p :: path
    cur := p
  return some path

/-- The axiom set of `root`, walking `idx`'s `uses` edges from it, with
`override`'s axiom set substituted for a constant it names instead of
following that constant's own edges (`docs/decisions.md` D15,
`docs/machine.md` § Acceptance): a proof-only repair changes one module's
declarations' own axiom sets, so every declaration that reaches one of them
gets the new set through this walk, with no rebuild. Each constant enters
the queue at most once, so `idx.size + override.size + 1` rounds visit
every one, the same bound `shortestPath` uses. -/
def axiomsBySubstitution (idx : Std.HashMap String Const)
    (override : Std.HashMap String (List String)) (root : String) : List String := Id.run do
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert root
  let mut queue : Array String := #[root]
  let mut axioms : Std.HashSet String := {}
  let mut i := 0
  for _ in [0:idx.size + override.size + 1] do
    let some n := queue[i]? | break
    i := i + 1
    match override[n]? with
    | some axs => for a in axs do axioms := axioms.insert a
    | none =>
      match idx[n]? with
      | none => pure ()
      | some c =>
        if let some a := c.axiomName then axioms := axioms.insert a
        for u in c.uses do
          unless seen.contains u do
            seen := seen.insert u
            queue := queue.push u
  pure (axioms.toList.toArray.qsort (· < ·)).toList

/-- A constant at one toolchain, under the first of `names` that it holds. -/
def presence (idx : Std.HashMap String Const) (owners : List (String × Owner))
    (names : List String) (shown : String) : Presence :=
  match names.findSome? (idx[·]?) with
  | some c => .present c.name c.module (owners.lookup c.module) c.axioms
  | none => .absent shown

/-- A name component Lean generates, not a person: it starts with `_`
(`List.find?_congr._proof_1_1`), or with `match_` (`allocationSizes.match_1`,
`docs/rules.md` § Axiom-finding rules, `causeTag`'s `matcher` case). -/
def generatedPart (part : String) : Bool := part.startsWith "_" || part.startsWith "match_"

/-- The names that the owner of a generated auxiliary can have. Lean gives
such a name a component, usually its last, that `generatedPart` holds
(`List.find?_congr._proof_1_1`, `allocationSizes.match_1`,
`allocationSizes._f`). Its owner is the name before the first such
component (`List.find?_congr`, `allocationSizes`). A private auxiliary has
the prefix `_private.<module>.0.`, as EquiVM run 10's
`_private.Mathlib.Data.List.Find.0.List.find?_congr._proof_1_1`: its owner
is the name after the prefix (a public declaration) or with it (a private
one). Empty for a name that is no auxiliary. -/
def ownerNames (n : String) : List String :=
  let parts := n.splitOn "."
  let (pre, rest) := if parts.head? == some "_private" then
      let mod := (parts.drop 1).takeWhile (·.toNat?.isNone)
      (("_private" :: mod) ++ (parts.drop (mod.length + 1)).take 1, parts.drop (mod.length + 2))
    else ([], parts)
  let head := rest.takeWhile (!generatedPart ·)
  if head.length == rest.length || head.isEmpty then []
  else [".".intercalate head] ++ (if pre.isEmpty then [] else [".".intercalate (pre ++ head)])

/-- Pick the cause on `path`: walk from the axiom toward the declaration, and
take the first constant that differs (`Link.differs`), without the axiom
itself. An auxiliary (`ownerNames`) gives its place to its owner when the
owner is on the path and differs too: the owner is the lemma that a person
reads. -/
def pickCause (path : List Link) : Option Link :=
  let inner := path.dropLast.reverse
  match inner.find? (·.differs) with
  | none => none
  | some c =>
    let os := ownerNames c.here.name
    some ((path.find? fun l => l.here.name ∈ os && l.differs).getD c)

/-- The explanation of one changed axiom `x` of a declaration: `here` is the
toolchain that has the axiom, `there` the other one. `root` and `rootThere`
are the declaration's names at each, `toThere` maps a name of `here` to the
names it can have at `there`. -/
def explainAxiom (here there : Side) (hIdx tIdx : Std.HashMap String Const)
    (toThere : String → List String) (root rootThere x : String) (change : Change) :
    AxiomExplanation :=
  match shortestPath hIdx root (·.axiomName == some x) with
  | none => .notComputed x change
      s!"at {here.toolchain} the probe's data has no path from {root} to {x}"
  | some names =>
    let path := names.map fun n =>
      { here := presence hIdx here.owners [n] n, there := presence tIdx there.owners (toThere n) n : Link }
    match pickCause path with
    | none => .notComputed x change
        s!"no constant on the path from {root} to {x} has a different axiom set at {there.toolchain}"
    | some c =>
      let otherPath := match c.there with
        | .absent n => .error s!"{n} does not exist at {there.toolchain}"
        | .present n .. =>
          match shortestPath tIdx rootThere (·.name == n) with
          | some p => .ok p
          | none => .error s!"at {there.toolchain} {rootThere} does not depend on {n}"
      .cause { axiom_ := x, change, path, cause := c, otherPath }

/-- The explanations of a Violation finding: one per axiom that the baseline
row `b` and the after row `a` do not share. -/
def explainViolation (names : Names) (base after : Side) (b a : Decl) : List AxiomExplanation :=
  let bIdx := base.index
  let aIdx := after.index
  let added := a.axioms.filter (· ∉ b.axioms)
  let removed := b.axioms.filter (· ∉ a.axioms)
  added.map (fun x => explainAxiom after base aIdx bIdx names.toBase a.name b.name x .added) ++
  removed.map fun x => explainAxiom base after bIdx aIdx (fun n => [names.toAfter n]) b.name a.name x .removed

/-- The names on the shortest path at `here` from each root to its axiom,
for `queries` `(root, axiom)`, mapped to the names they can have at the other
toolchain. The constants of a path that does not reach the axiom at the
other toolchain are not in the closure of the declaration there, so the
probe there must report them as roots before `explainViolation` can compare
them. -/
def pathLookups (here : Side) (queries : List (String × String))
    (toThere : String → List String) : List String :=
  let idx := here.index
  (queries.flatMap fun (root, x) =>
    ((shortestPath idx root (·.axiomName == some x)).getD []).flatMap toThere).eraseDups

/-- The data of two probe runs at one toolchain: every constant once. -/
def Side.merge (a b : Side) : Side :=
  let idx := a.index
  let consts := a.consts ++ b.consts.filter (!idx.contains ·.name)
  let held := (consts.foldl (fun s c => s.insert c.name) ({} : Std.HashSet String))
  { toolchain := a.toolchain, consts,
    owners := a.owners ++ b.owners.filter fun (m, _) => (a.owners.lookup m).isNone,
    missing := (a.missing ++ b.missing).eraseDups.filter (!held.contains ·) }

/-- What a group of findings shares: one cause constant, or one reason that
the cause is not computed. -/
inductive CauseKey where
  | const (name module : String) (change : Change)
  | notComputed (reason : String)
  deriving DecidableEq, Repr

/-- The key of one explanation. -/
def AxiomExplanation.key : AxiomExplanation → CauseKey
  | .cause c =>
    match c.cause.here with
    | .present n m .. => .const n m c.change
    | .absent n => .const n "" c.change
  | .notComputed _ _ r => .notComputed r

/-- One cause and the findings it explains: for each, the card id, the
declaration and the axioms. -/
structure CauseGroup where
  key : CauseKey
  /-- The first explanation with this key, for the cause's data. -/
  first : AxiomExplanation
  members : List (String × String × List String)
  deriving Repr

/-- Group the explanations of the cards `(id, declaration, explanations)` by
cause, in the order of first appearance. A card is in one group per distinct
cause of its axioms. -/
def groupCauses (cards : List (String × String × List AxiomExplanation)) : List CauseGroup :=
  cards.foldl (init := []) fun gs (id, decl, xs) =>
    xs.foldl (init := gs) fun gs x =>
      let ax := match x with | .cause c => c.axiom_ | .notComputed a _ _ => a
      match gs.findIdx? (·.key == x.key) with
      | some i => gs.modify i fun g =>
        match g.members.findIdx? (·.1 == id) with
        | some j => { g with members := g.members.modify j fun (i', d, as) => (i', d, as ++ [ax]) }
        | none => { g with members := g.members ++ [(id, decl, [ax])] }
      | none => gs ++ [{ key := x.key, first := x, members := [(id, decl, [ax])] }]

/-! ## Level 3: the site of an axiom finding -/

/-- Whether a constant's presence belongs to the target: its module's owner
package is neither Lean core nor a dependency package (decision D14,
`docs/machine.md` § The site of an axiom finding). `rootPackage` is the
target's own package name (`Owner.package` of the target's own modules,
`docs/verification.md` § The data at each toolchain). An absent constant, or
one with no recorded owner, is not owned. -/
def Presence.owned (rootPackage : String) : Presence → Bool
  | .present _ _ (some o) _ => o.package == rootPackage
  | .present _ _ none _ => false
  | .absent _ => false

/-- The declaration name and module of a `Presence`, for a site: a generated
auxiliary (`ownerNames`) gives its place to the declaration that owns it,
the same rule `pickCause` already applies to the cause, because the site
must be a declaration a person can edit. The module is empty for an absent
constant, which never happens for an owned one. -/
def Presence.site : Presence → String × String
  | .present n m .. => ((ownerNames n).head?.getD n, m)
  | .absent n => ((ownerNames n).head?.getD n, "")

/-- The site of an axiom finding (decision D14, `docs/machine.md` § The site
of an axiom finding): walking `c.path` from the axiom toward the
declaration, the first owned constant before `c.cause`, or the declaration
itself (`c.path[0]`) when no such constant exists. Formally, with `k` the
index of `c.cause` on `c.path`, the site is `c.path[i]`'s owner, for the
largest `i < k` with `c.path[i]` owned, or `c.path[0]`'s owner. `c.path[0]`
is always the finding's own declaration, which is always owned, so the site
always exists. -/
def siteOf (rootPackage : String) (c : AxiomCause) : String × String :=
  let d := (c.path.head?.map (·.here.site)).getD ("", "")
  match c.path.findIdx? (· == c.cause) with
  | none => d
  | some k =>
    match (c.path.take k).reverse.find? (·.here.owned rootPackage) with
    | some l => l.here.site
    | none => d

/-- What a group of findings sharing one site and one cause have in common
(decision D14): the site declaration, and `CauseGroup`'s own key. A
`FindingSite` is one such group (`docs/machine.md` § `FindingSite`). -/
structure SiteKey where
  site : String × String
  cause : CauseKey
  deriving DecidableEq, Repr

/-- One site, the cause every member shares, and the findings it closes: for
each, the card id, the declaration and the axioms. The first explanation
with this key gives the site's and the cause's data. -/
structure FindingSiteGroup where
  key : SiteKey
  first : AxiomCause
  members : List (String × String × List String)
  deriving Repr

/-- Group the explanations of the cards `(id, declaration, explanations)` by
site, in the order of first appearance (decision D14). A finding with no
computed cause (`AxiomExplanation.notComputed`) has no path and so no site;
it is not in any `FindingSiteGroup`. A card is in one group per distinct
`(site, cause)` pair of its axioms. -/
def groupFindingSites (rootPackage : String)
    (cards : List (String × String × List AxiomExplanation)) : List FindingSiteGroup :=
  cards.foldl (init := []) fun gs (id, decl, xs) =>
    xs.foldl (init := gs) fun gs x =>
      match x with
      | .notComputed .. => gs
      | .cause c =>
        let key : SiteKey := { site := siteOf rootPackage c, cause := x.key }
        match gs.findIdx? (·.key == key) with
        | some i => gs.modify i fun g =>
          match g.members.findIdx? (·.1 == id) with
          | some j => { g with members := g.members.modify j fun (i', d, as) => (i', d, as ++ [c.axiom_]) }
          | none => { g with members := g.members ++ [(id, decl, [c.axiom_])] }
        | none => gs ++ [{ key, first := c, members := [(id, decl, [c.axiom_])] }]

/-! ## Level 3: matching an axiom-finding rule to a site -/

/-- The error class of an axiom finding, from its cause's `Change` field
(decision D13, `docs/rules.md` § Axiom-finding rules). `classify` stays a
function of `Diagnostic` only; this is the analogous total function over
`AxiomCause`, so neither function grows a case the other must also handle. -/
def classifyCause (c : AxiomCause) : ErrorClass :=
  match c.change with
  | .added => .axiomsAdded
  | .removed => .axiomsRemoved

/-- Whether a rule's `causeTag` matches a site's own tag (`docs/rules.md` §
Axiom-finding rules): `none` is a rule for a class other than
`axiomsAdded`/`axiomsRemoved`, which `findingRuleCandidates` already excludes
by `classifyCause` before this check runs, so `none` matching every tag costs
nothing; `some .any` also matches every tag; `some t` matches only a site
whose own tag is `t`. -/
def causeTagMatches : Option CauseTag → CauseTag → Bool
  | none, _ => true
  | some .any, _ => true
  | some t, u => t == u

/-- Candidates from one rule for one finding site (`docs/rules.md` §
Axiom-finding rules): the trigger proposes a rule's candidates the same way
`ruleCandidates` (`LeanMend/Core/Ops.lean`) does for a diagnostic's site:
match the rule's class against `classifyCause`, then its `causeTag` against
the site's own tag, then its `node` against the syntax `causeTactic` finds
(`docs/machine.md` § The tactic inside the site). `heartbeats` and
`setOptionBefore` need only the declaration's insertion point, `declStart`
(decision D17's `mutualStart` when the declaration sits inside a `mutual`
block); `replaceInBody` needs the declaration's own body text and start
(`body`), the same text `ruleCandidates` reads from a diagnostic's `Site`;
every other operation edits the tactic node. A site with no such node gets
no candidate from an operation that needs one, the same rule a diagnostic
site with no node already follows. -/
def findingRuleCandidates (r : Rule) (tag : CauseTag) (cause : AxiomCause) (decl : String)
    (declStart : Nat) (node : Option Node) (body : Option (Nat × String)) : List Candidate :=
  if classifyCause cause != r.cls || !causeTagMatches r.causeTag tag then [] else
  r.ops.filterMap fun op =>
    match op with
    | .heartbeats n =>
      let repl := s!"set_option maxHeartbeats {n} in\n"
      some { rule := s!"{r.name}: {repr op}", entrenchment := r.entrenchment,
             target := .beforeDecl decl, start := declStart, stop := declStart,
             replacement := repl, tokens := addedTokens "" repl }
    | .setOptionBefore name value =>
      let repl := s!"set_option {name} {value} in\n"
      some { rule := s!"{r.name}: {repr op}", entrenchment := r.entrenchment,
             target := .beforeDecl decl, start := declStart, stop := declStart,
             replacement := repl, tokens := addedTokens "" repl }
    | .replaceInBody d old new => do
      guard (d == decl)
      let (bodyStart, bodyText) ← body
      -- exactly one occurrence, at a known byte offset, mirroring `ruleCandidates`.
      match bodyText.splitOn old with
      | [before, _] =>
        let a := bodyStart + before.utf8ByteSize
        pure { rule := s!"{r.name}: {repr op}", entrenchment := r.entrenchment,
               target := .body d, start := a, stop := a + old.utf8ByteSize,
               replacement := new, tokens := addedTokens old new }
      | _ => none
    | _ => do
      let n ← node
      let repl ← applyOp op n
      pure { rule := s!"{r.name}: {repr op}", entrenchment := r.entrenchment,
             target := .body decl, start := n.start, stop := n.stop,
             replacement := repl, tokens := addedTokens n.text repl }

/-- Candidates for one `FindingSiteGroup`: every matching rule's candidates,
ratified rules before proposed, each in rule-list order (`docs/rules.md` §
Entrenchment and order; the same order `proposeAll` gives a diagnostic
site's candidates). -/
def findingCandidates (rules : List Rule) (tag : CauseTag) (g : FindingSiteGroup)
    (declStart : Nat) (node : Option Node) (body : Option (Nat × String)) : List Candidate :=
  let byE (e : Entrenchment) :=
    (rules.filter (·.entrenchment == e)).flatMap
      fun r => findingRuleCandidates r tag g.first g.key.site.1 declStart node body
  byE .ratified ++ byE .proposed

/-! ## Behavior: the body change -/

/-- The body of a declaration at one toolchain: its text, the byte offset
where it starts in its file, and the maximal ranges of the proofs inside it,
in file offsets (the probe's `proofs`). -/
structure Body where
  text : String
  start : Nat
  proofs : List (Nat × Nat)
  deriving Repr, DecidableEq

/-- One hunk of a line diff: the lines it removes and adds, their first line
in each body (from 0), and the changed bytes in file offsets, after the
bytes that both texts of the hunk share at their start and at their end. -/
structure Hunk where
  removed : List String
  added : List String
  beforeLine : Nat
  afterLine : Nat
  beforeSpan : Nat × Nat
  afterSpan : Nat × Nat
  deriving Repr, DecidableEq

/-- The edit script of a longest common subsequence of `a` and `b`:
`(true, i, j)` keeps `a[i] = b[j]`, `(false, i, j)` is a change at `a[i]`,
`b[j]`. Returned as the list of kept index pairs, in order. -/
def lcsPairs (a b : Array String) : List (Nat × Nat) := Id.run do
  let n := a.size
  let m := b.size
  -- `t[i][j]`: the length of the LCS of `a[i:]` and `b[j:]`.
  let mut t : Array (Array Nat) := Array.replicate (n + 1) (Array.replicate (m + 1) 0)
  for ii in [0:n] do
    let i := n - 1 - ii
    let mut row := Array.replicate (m + 1) 0
    for jj in [0:m] do
      let j := m - 1 - jj
      let v := if a[i]! == b[j]! then t[i + 1]![j + 1]! + 1
        else max t[i + 1]![j]! row[j + 1]!
      row := row.set! j v
    t := t.set! i row
  let mut out := []
  let mut i := 0
  let mut j := 0
  for _ in [0:n + m] do
    if i < n && j < m then
      if a[i]! == b[j]! then
        out := (i, j) :: out
        i := i + 1
        j := j + 1
      else if t[i + 1]![j]! ≥ t[i]![j + 1]! then i := i + 1
      else j := j + 1
  return out.reverse

/-- The byte offset where each line of `s` starts, and one more entry: the
size of `s`. -/
def lineStarts (s : String) : Array Nat := Id.run do
  let lines := s.splitOn "\n"
  let mut out := #[]
  let mut pos := 0
  for l in lines do
    out := out.push pos
    pos := pos + l.utf8ByteSize + 1
  return out.push s.utf8ByteSize

/-- The bytes that `a` and `b` share at their start, and then at their end. -/
def commonEnds (a b : ByteArray) : Nat × Nat := Id.run do
  let n := min a.size b.size
  let mut p := 0
  for k in [0:n] do
    if a[k]! == b[k]! then p := k + 1 else break
  let mut s := 0
  for k in [0:n - p] do
    if a[a.size - 1 - k]! == b[b.size - 1 - k]! then s := k + 1 else break
  return (p, s)

/-- The hunks of the line diff from `before` to `after`. -/
def diffHunks (before after : Body) : List Hunk := Id.run do
  let a := (before.text.splitOn "\n").toArray
  let b := (after.text.splitOn "\n").toArray
  let sa := lineStarts before.text
  let sb := lineStarts after.text
  let keep := lcsPairs a b ++ [(a.size, b.size)]
  let mut out := []
  let mut i := 0
  let mut j := 0
  for (ki, kj) in keep do
    if ki > i || kj > j then
      let bytesA := before.text.toUTF8.extract sa[i]! (min sa[ki]! before.text.utf8ByteSize)
      let bytesB := after.text.toUTF8.extract sb[j]! (min sb[kj]! after.text.utf8ByteSize)
      let (p, s) := commonEnds bytesA bytesB
      out := out ++ [{ removed := (a.extract i ki).toList, added := (b.extract j kj).toList,
                       beforeLine := i, afterLine := j,
                       beforeSpan := (before.start + sa[i]! + p, before.start + sa[i]! + bytesA.size - s),
                       afterSpan := (after.start + sb[j]! + p, after.start + sb[j]! + bytesB.size - s) }]
    i := ki + 1
    j := kj + 1
  return out

/-- Whether the changed bytes `span` lie inside one of `proofs`. An empty
span is the point where the other toolchain's text has bytes that this one
has not: it counts when it lies inside a proof or at one of its ends. The
other side's bytes are not empty, and `bodyChange` checks them inside a
proof of their own toolchain, so a point at an end cannot let data in. -/
def inProof (proofs : List (Nat × Nat)) (span : Nat × Nat) : Bool :=
  let (s, e) := span
  proofs.any fun (a, b) => if s < e then a ≤ s && e ≤ b else a ≤ s && s ≤ b

/-- The body change of a Behavior finding: the hunks, and the hunks whose
changed bytes do not lie inside a proof at both toolchains. The change is in
proofs only when that list is empty and some hunk exists. -/
structure BodyChange where
  hunks : List Hunk
  outside : List Hunk
  deriving Repr

def bodyChange (before after : Body) : BodyChange :=
  let hunks := diffHunks before after
  { hunks, outside := hunks.filter fun h =>
      !(inProof before.proofs h.beforeSpan && inProof after.proofs h.afterSpan) }

def BodyChange.proofOnly (c : BodyChange) : Bool := !c.hunks.isEmpty && c.outside.isEmpty

/-- A commit from the baseline commit to the tip of `lean-mend/mend` that
changed a declaration's body (`git log -L`). -/
structure BodyCommit where
  sha : String
  subject : String
  /-- The `Rule:` line that lean-mend writes in each of its commits. The
  bump commit has none. -/
  rule : Option String
  /-- The commit is the bump commit, the input of `--adopt`: the commit where
  `lean-mend/mend` starts, not a commit of the run. -/
  bump : Bool
  deriving Repr, DecidableEq

/-- What the cards of one run need, saved in the session
(`docs/verification.md` § What a card explains). -/
structure Evidence where
  base : Side
  after : Side
  /-- The body of each Behavior finding at each toolchain, by the
  declaration's name at the new toolchain. -/
  bodies : List (String × Body × Body)
  /-- The commits that changed each finding's body, by the declaration's
  name at the new toolchain. -/
  commits : List (String × List BodyCommit)
  deriving Repr

/-- Group the Behavior cards `(id, declaration, commits)` by the commits that
changed their bodies, in the order of first appearance. -/
def groupBodies (cards : List (String × String × List BodyCommit)) :
    List (List BodyCommit × List (String × String)) :=
  cards.foldl (init := []) fun gs (id, decl, cs) =>
    match gs.findIdx? (·.1 == cs) with
    | some i => gs.modify i fun (k, ms) => (k, ms ++ [(id, decl)])
    | none => gs ++ [(cs, [(id, decl)])]

end LeanMend
