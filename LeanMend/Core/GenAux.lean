import LeanMend.Core.Cause
import LeanMend.Core.DepDiff
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Generated auxiliaries of the target (`docs/static-diff.md` § 3)

Some changes live in a generator, not in a constant: the match compiler, the
equation compiler, `deriving` handlers, structural or well-founded recursion.
Their output is a set of auxiliary constants in the target's own build, under
names Lean itself picks, which can differ between toolchains
(`docs/static-diff.md` § 3). This module compares each target declaration's
auxiliaries at the two sides, matched by **owner and role**, never by name.

Owner detection reuses `ownerNames`/`generatedPart`
(`LeanMend.Core.Cause`, decision D14): the same rule that already gives a
`match_N` or `_proof_N` auxiliary's place to its owning declaration for an
axiom finding's site. One more generated shape is added here, a `deriving`
handler's own output (`docs/verification.md` § The certificate,
`instInhabitedPools.default`), which carries no `_`/`match_`-prefixed
component.
-/

namespace LeanMend

/-- The role Lean's generators give an auxiliary constant, told apart by its
name's generated component: the match compiler's matcher, an equation
lemma, a sparse `casesOn` auxiliary (`backward.match.sparseCases`,
`docs/machine.md` § Acceptance), the well-founded-recursion helper `_f`
(`docs/machine.md` § The site of an axiom finding), another structural or
well-founded encoding, or a `deriving` handler's own output. `other` is a
generated name (`ownerNames` gives it an owner) whose component matches no
known role; it is still compared, under its own owner. -/
inductive AuxRole where
  | matcher
  | eqnLemma
  | sparseCasesOn
  | wfHelperF
  | structuralWF
  | derivingOutput
  | other
  deriving DecidableEq, Repr, Inhabited

/-- `AuxRole`'s wire name, for the CLI's JSON and a card's report. -/
def AuxRole.tag : AuxRole → String
  | .matcher => "matcher"
  | .eqnLemma => "eqnLemma"
  | .sparseCasesOn => "sparseCasesOn"
  | .wfHelperF => "wfHelperF"
  | .structuralWF => "structuralWF"
  | .derivingOutput => "derivingOutput"
  | .other => "other"

/-- The role of a generated name's own last component (`auxOwnerRole`'s
`comp`): lower-cased first, so a capitalization difference between
toolchains (Lean has renamed auxiliary components before,
`docs/static-diff.md` "the release notes … mention `_sparseCasesOn`
auxiliaries only for a private-name defect") does not change the role. -/
def auxRoleOfComponent (c : String) : AuxRole :=
  let lc := c.toLower
  if lc.startsWith "match_" then .matcher
  else if lc == "_f" then .wfHelperF
  else if lc.startsWith "eq_" || lc.startsWith "_eq_" then .eqnLemma
  else if (lc.splitOn "sparse").length > 1 then .sparseCasesOn
  else if lc.startsWith "_unary" || lc.startsWith "_wf" || lc.startsWith "_terminat" ||
      lc.startsWith "_brecon" || lc == "_ind" then .structuralWF
  else if lc == "default" then .derivingOutput
  else .other

/-- The owner and the role of a generated auxiliary `n`: `ownerNames`
(reused unchanged, `LeanMend.Core.Cause`) finds the owner from a
`_`/`match_`-prefixed component; its last result (the private-prefixed
form when `n` has one, else the same as its first) gives the exact index
of the generated component in `n`'s own dot-separated parts, so the role
reads the right component even under a private prefix. When `ownerNames`
finds no owner (no `_`/`match_` component), one more generated shape is
tried: a `deriving` handler's own output, whose last component is exactly
`default` with no such prefix (`docs/verification.md` § The certificate).
`none` for a name that is nobody's generated auxiliary: a target
declaration itself, already a certificate row. -/
def auxOwnerRole (n : String) : Option (String × AuxRole) :=
  let parts := n.splitOn "."
  match ownerNames n with
  | [] =>
    let last := parts.getLast!
    if parts.length < 2 then none
    else if last == "default" then some (".".intercalate parts.dropLast, .derivingOutput)
    -- An equation lemma (`f.eq_1`, …, `f.eq_def`, `Lean.Meta.Eqns`): no
    -- `_`/`match_` prefix, so `generatedPart` does not catch it, and
    -- without this case it is wrongly treated as a real declaration — its
    -- own BFS root in `reachableAux` then rediscovers the owner's matcher
    -- through the equation lemma's own proof term (which cites the
    -- matcher to state the unfolding), reattaching a stale axiom the
    -- owner's real compiled value never reaches (measured on EquiVM's
    -- pins: `allocationSizes.eq_N` made the before side falsely reach
    -- `allocationSizes.match_1`, masking the real E3 finding). -/
    else if last == "eq_def" || (last.startsWith "eq_" && (last.drop 3).toNat?.isSome) then
      some (".".intercalate parts.dropLast, .eqnLemma)
    else none
  | names =>
    let idx := (names.getLast!.splitOn ".").length
    some (names.head!, auxRoleOfComponent (parts.getD idx ""))

/-- One generated auxiliary of one target declaration at one side: its own
`DepConst` (name, module, kind, axioms, body hash), its owner and its
role. -/
structure AuxConst where
  owner : String
  role : AuxRole
  const : DepConst
  deriving Repr, DecidableEq

/-- A root declaration: a name `auxOwnerRole` gives no owner to — the
target's own declarations, the certificate's rows, never a generated
auxiliary itself. -/
def isRoot (name : String) : Bool := (auxOwnerRole name).isNone

/-- The generated auxiliaries reachable from `root`'s own compiled value,
breadth first over `uses` (the same walk shape `Cause.shortestPath`
already runs over a `uses`-carrying index, reused here in form): a
generated name Lean emits but `root`'s own value never calls is not
counted as `root`'s auxiliary, even when its name's shape would suggest
the same owner.

This guard is load-bearing, not a simplification: Lean's equation
compiler emits more than one `match_N` per declaration when a match has
more than one case split, and only one of them is on the path the
compiled value (the `_unsafe_rec`/`_f` form) actually calls — the others
exist only to state equation lemmas for `simp`, and are never reached.
Measured on EquiVM's pins: at v4.29.0, `Stele.Interp.allocationSizes`'s
own `uses` is `[Stele.Expr, List, Inhabited.default,
Ethereum.Stack.instInhabited]` — none of `match_1`/`match_3`/`match_5`/
`match_7`, even though `match_7`'s own axiom set there already has
`propext` (an equation-lemma artifact, unreached). At v4.33.1, by
contrast, `allocationSizes` itself uses `allocationSizes._f`, which uses
`allocationSizes.match_1` (axioms `[propext]`): the real path (`probe
explain`, two runs on EquiVM's `mend-cache/probe-base` and `mend-target`,
2026-11-11). Grouping every same-named-pattern auxiliary of one module
unconditionally (an earlier draft of this function) put the unreached
`match_7` into the same union as the reached `match_1`, which made both
sides' unions already contain `propext` and so reported no entry at all
for the real E3 finding — the walk below is the fix.

The group key this walk emits is `root`, not the name-parsed owner
`auxOwnerRole` would give the discovered auxiliary. These differ in one
more EquiVM case: `allocationSizes`'s own `where`-bound helper, `refExprs`,
compiles its own inner match (`r.steps.filterMap fun | .mindex e | …`); at
v4.29.0 Lean names it flatly under the parent's own numbering,
`allocationSizes.match_1` (not `allocationSizes.refExprs.match_1`), even
though `refExprs`'s own `uses` is what reaches it, not `allocationSizes`'s.
Keying by the name-parsed owner would attribute it to `allocationSizes`
regardless of which root's walk found it, reattaching a stale,
unconnected axiom the same way the unbounded grouping did. `root` is a
real, stable declaration name at both toolchains (`refExprs` exists at
both pins); the auxiliary's own generated name is not. -/
def reachableAux (idx : Std.HashMap String DepConst) (root : String) : List AuxConst := Id.run do
  let some _ := idx[root]? | return []
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert root
  let mut queue : Array String := #[root]
  let mut out : List AuxConst := []
  let mut i := 0
  for _ in [0:idx.size + 1] do
    let some n := queue[i]? | break
    i := i + 1
    let some c := idx[n]? | continue
    for u in c.uses do
      unless seen.contains u do
        seen := seen.insert u
        -- A real declaration (`isRoot u`) is a boundary: `root` reaches it,
        -- but not what lies beyond it — that belongs to `u`'s own walk,
        -- when `u` is iterated as a root in its turn (`allReachableAux`).
        -- Without this stop, an unrelated declaration elsewhere that calls
        -- `root` through a `simp`-unfolded equation lemma would make
        -- `root`'s own reachable set absorb that caller's whole further
        -- closure too, the same cross-contamination the module-wide
        -- grouping already showed (this doc comment's own measurement):
        -- on EquiVM's pins, an unbounded walk made the before side falsely
        -- reach `allocationSizes.match_1` through the `refExprs` boundary.
        if isRoot u then continue
        match auxOwnerRole u, idx[u]? with
        | some (owner, role), some uc =>
          -- An auxiliary is `root`'s only when its name-parsed owner is `root`
          -- or a namespace ancestor of `root` (a `where` helper's match that
          -- Lean numbers under the parent, above). Any other generated name
          -- belongs to another declaration (on EquiVM's pins, 227 of 228
          -- predictions were another declaration's `eq_1`, reached through
          -- a proof) and is a boundary, like a real declaration.
          if owner == root || (owner ++ ".").isPrefixOf root then
            queue := queue.push u
            out := out ++ [{ owner := root, role, const := uc }]
        | _, _ => queue := queue.push u
  pure out

/-- Every generated auxiliary of one side that some root declaration's own
compiled value actually reaches (`reachableAux`, one walk per root — the
target's own declarations, bounded by the target's own size, never the
whole dependency set). -/
def allReachableAux (consts : List DepConst) : List AuxConst :=
  let idx := ownIndex consts
  let roots := consts.filterMap fun c => if isRoot c.name then some c.name else none
  roots.flatMap (reachableAux idx)

/-- The axiom set and body-hash set of a group of auxiliaries that share
one owner and role (more than one reachable auxiliary of the same role
under one owner — for example two matchers in one `match`-heavy body — is
compared as one set, not paired by index: Lean's own numbering of
`match_1`, `match_2` is not guaranteed stable across toolchains either).
Proof irrelevance (decision D16) drops the body from the comparison for a
`theorem`-kind auxiliary (a `_proof_N` helper, always irrelevant under
proof irrelevance, `docs/static-diff.md` Finding 4 of the design review):
only its axiom set matters, the same skip `depDiff` already applies to a
dependency `theorem`. -/
structure AuxGroup where
  axioms : List String
  bodyHashes : List String
  deriving Repr, DecidableEq

def groupOf (cs : List AuxConst) : AuxGroup :=
  let axioms := ((cs.flatMap (·.const.axioms)).eraseDups.toArray.qsort (· < ·)).toList
  let bodyHashes :=
    let hs := cs.filterMap fun (c : AuxConst) => if c.const.kind == "theorem" then none else c.const.bodyHash
    (hs.eraseDups.toArray.qsort (· < ·)).toList
  { axioms, bodyHashes }

/-- The reachable auxiliaries of one side, grouped by owner and role,
keyed by one string (`owner ++ '\0' ++ role.tag`: `Std.HashMap` needs
`BEq` and `Hashable`, which `String` already has and a hand-written
`AuxRole` instance would add for no benefit): more than one entry for the
group keeps insertion order, for `groupOf`'s union. -/
def auxKey (owner : String) (role : AuxRole) : String := owner ++ "\x00" ++ role.tag

def auxIndex (consts : List DepConst) : Std.HashMap String (List AuxConst) :=
  (allReachableAux consts).foldl (fun m a =>
    let k := auxKey a.owner a.role
    m.insert k ((m.getD k []) ++ [a])) {}

/-- What changed about one owner declaration's one role of generated
auxiliary between the two sides: the same shape `DepDiffKind` already
gives a dependency constant (decision S2) — an axiom-set change, a body
change (never for a `theorem`-kind group), or existence at one side only. -/
abbrev GenAuxKind := DepDiffKind

/-- One entry of the generated-auxiliary diff (`docs/static-diff.md` § 3):
one target declaration (`owner`), one role, and what changed, with one
auxiliary named at each side where the role exists (the first one found,
when a role has more than one — `groupOf`'s own doc comment on why they
are compared as a set, not paired). -/
structure GenAuxEntry where
  owner : String
  role : AuxRole
  kind : GenAuxKind
  before : Option AuxConst
  after : Option AuxConst
  deriving Repr, DecidableEq

/-- The generated-auxiliary diff (`docs/static-diff.md` § 3): pure over
each side's own-module constants, restricted to what some root's own
value actually reaches (`allReachableAux`). A `(owner, role)` present at
both sides with the same axiom set and the same body-hash set is not an
entry. An axiom-set change wins over a body change when both differ, the
same precedence `depDiff` uses and for the same reason (`LeanMend.depDiff`'s
own doc comment). -/
def genAuxDiff (before after : List DepConst) : List GenAuxEntry :=
  let bIdx := auxIndex before
  let aIdx := auxIndex after
  let keys := (bIdx.toList.map (·.1) ++ aIdx.toList.map (·.1)).eraseDups
  -- `auxIndex` never stores an empty list for a key (every insert adds one
  -- element), so the head of a found group always exists: matched here by
  -- pattern, not `head!`, so no `Inhabited AuxConst` instance is needed.
  keys.filterMap fun key =>
    match bIdx[key]?, aIdx[key]? with
    | some (b0 :: bRest), some (a0 :: aRest) =>
      let bg := groupOf (b0 :: bRest)
      let ag := groupOf (a0 :: aRest)
      if bg.axioms != ag.axioms then
        some { owner := b0.owner, role := b0.role,
               kind := .axioms (ag.axioms.filter (· ∉ bg.axioms)) (bg.axioms.filter (· ∉ ag.axioms)),
               before := some b0, after := some a0 }
      else if bg.bodyHashes != ag.bodyHashes then
        some { owner := b0.owner, role := b0.role, kind := .body, before := some b0, after := some a0 }
      else none
    | some (b0 :: _), none =>
        some { owner := b0.owner, role := b0.role, kind := .onlyBefore, before := some b0, after := none }
    | none, some (a0 :: _) =>
        some { owner := a0.owner, role := a0.role, kind := .onlyAfter, before := none, after := some a0 }
    | some [], _ | _, some [] | none, none => none

/-- A predicted Violation (`docs/static-diff.md` § 3): a target declaration
whose auxiliary gains an axiom, the axioms gained, and the auxiliary named
as cause (its name at the after side, the toolchain that has the gain).
Two shapes predict a gain: an existing auxiliary's axiom set grows
(`.axioms` with a nonempty `added`), or a brand-new auxiliary appears at
the after side carrying a nonempty axiom set of its own (`.onlyAfter`) —
EquiVM's own E3 (`allocationSizes.match_1`/`allocationSizes._f`, neither
reachable from `allocationSizes` at v4.29.0, both reachable at v4.33.1
with `propext`) is the second shape. A body-only change, an axiom
removal with no addition, or an auxiliary present at the before side only,
is reported (`genAuxDiff`) but predicts no Violation. -/
structure GenAuxPrediction where
  owner : String
  role : AuxRole
  added : List String
  cause : String
  deriving Repr, DecidableEq

def predictionsOf (es : List GenAuxEntry) : List GenAuxPrediction :=
  es.filterMap fun e => match e.kind, e.after with
    | .axioms added _, some a =>
        if added.isEmpty then none else some { owner := e.owner, role := e.role, added, cause := a.const.name }
    | .onlyAfter, some a =>
        if a.const.axioms.isEmpty then none
        else some { owner := e.owner, role := e.role, added := a.const.axioms, cause := a.const.name }
    | _, _ => none

end LeanMend
