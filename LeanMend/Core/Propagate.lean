import LeanMend.Core.DepDiff
import LeanMend.Core.Cause
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Propagation through the target (`docs/static-diff.md` § 2)

A bump's finding is knowable before any repair runs, in two parts: § 1 (the
dependency diff, `LeanMend.Core.DepDiff`) finds which dependency constants
changed, independent of any target; this module maps that diff to the
target declarations that reach a changed constant, with the predicted axiom
change and the shortest path (the same form a Violation card's cause
already takes, `Core/Cause.lean`'s `shortestPath`).

This module is the pure Core half: it takes the dependency diff and the
target's own after-side constant graph, already gathered by the shell from
one batched probe call (`LeanMend.Shell.Propagate`, `export --own`), and
computes the predictions with no IO.
-/

namespace LeanMend

/-! The target's own after-side constants are `DepConst` rows, as the
probe's `export --own` reports them (`probe/Probe.lean`, `cmdExportOwn`):
their kind (`kindOf`), their own full axiom set (`axiomsOf`), and the
immediate constants `axEdges` reaches — one hop, an own name or a
dependency name, not walked further. Their `bodyHash` is `none`: a
dependency constant's own body hash comes from the dependency diff
(`DepDiffEntry`), not from this call. `axioms` is what tells a genuine new
reach (the declaration did not have the axiom before) from one the
declaration already had through an unrelated path (`baselineAxioms`,
`propagate`): without it, every declaration that reaches a changed
dependency constant for ANY reason gets a prediction, not only the ones
the change is actually new to — measured on EquiVM's pins, over 100 000
spurious predictions against 42 real ones before this field existed. -/

/-- The reverse of `uses`: for every name an own constant's edge reaches
(an own name or a dependency name), the own constants whose own edge
reaches it directly. A dependency name is a key only when some own
constant uses it directly; it is never itself a value, because `cs`
holds only own constants, so the walk below never steps past a
dependency name into its own, unrecorded edges — propagation reads only
the boundary the target's own declarations draw around the dependency
closure (`docs/static-diff.md` § 2), never a dependency constant's own
further uses. -/
def reverseUses (cs : List DepConst) : Std.HashMap String (List String) :=
  cs.foldl (init := ({} : Std.HashMap String (List String))) fun m c =>
    c.uses.foldl (fun m u => m.insert u ((m.getD u []) ++ [c.name])) m

/-- Every own declaration that reaches `goal` (an own name or a dependency
name) over the reverse graph `rev` (`reverseUses`, built once for the
whole step — `docs/static-diff.md` § Cost: rebuilding it per dependency
entry would cost one own-graph-sized map build per entry, hundreds to
thousands of times over on a real target, not once), each with the
shortest path to it, declaration first and `goal` last (the same order
`AxiomCause.path` already uses) — one breadth-first walk backward from
`goal`, instead of one forward walk per declaration (`Core/Cause.lean`'s
`shortestPath` walks forward from one root to one goal; this walks
backward from one goal to every root, so the whole step costs one walk
per dependency entry of interest, not one per own declaration, the
batched-probe-call discipline of `docs/static-diff.md` § Cost applied to
the pure walk too). `bound` is `cs.length + 1`: each name enters the
queue at most once (`goal` itself, then only own names — `reverseUses`'s
values are always own names), so that many rounds (one per name popped)
visit every one. -/
def reachersOf (bound : Nat) (rev : Std.HashMap String (List String)) (goal : String) :
    Std.HashMap String (List String) :=
  Id.run do
  let mut found : Std.HashMap String (List String) := {}
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert goal
  let mut queue : Array String := #[goal]
  let mut i := 0
  for _ in [0:bound] do
    let some n := queue[i]? | break
    i := i + 1
    let tail := found.getD n [n]
    for p in rev.getD n [] do
      unless seen.contains p do
        seen := seen.insert p
        found := found.insert p (p :: tail)
        queue := queue.push p
  pure found

/-- The predicted axiom change of one target declaration (`docs/static-diff.md`
§ 2): its path reaches a dependency constant whose own axiom set changed
(`DepDiffKind.axioms`) or that is new at the after side
(`DepDiffKind.onlyAfter`, whose own axioms are what it adds to the path). -/
structure AxiomPrediction where
  decl : String
  module : String
  axiomsAdded : List String
  axiomsRemoved : List String
  cause : String
  causeModule : String
  /-- The shortest path at the after side, declaration first, the changed
  dependency constant last. -/
  path : List String
  deriving Repr, DecidableEq, Inhabited

/-- The predicted Behavior cause of one target `def`, `instance` or
`abbrev` that computes through a dependency whose body changed
(`DepDiffKind.body`, `docs/static-diff.md` § 2) — never a `theorem`:
proof irrelevance (`docs/decisions.md` D16) already makes a theorem's own
proof term carry no signal `DepDiff.depDiff` acts on (it never marks a
`theorem`-kind dependency constant's body changed, and a `theorem`
target declaration is excluded here the same way, for the same reason). -/
structure BehaviorPrediction where
  decl : String
  module : String
  cause : String
  causeModule : String
  path : List String
  deriving Repr, DecidableEq, Inhabited

structure Predictions where
  axioms : List AxiomPrediction
  behavior : List BehaviorPrediction
  deriving Repr, DecidableEq

/-- A `def`, `instance` or `abbrev` computes; a `theorem` does not
(decision D16). -/
def computes (kind : String) : Bool :=
  kind == "def" || kind == "instance" || kind == "abbrev"

/-- The declaration a raw reached name stands for: a generated auxiliary
gives its place to its owner (`ownerNames`, `Core/Cause.lean`, the same
fold `pickCause` and `Cause.siteOf` already apply to a Violation card's
cause and site), so the predicted declaration is always one a person can
read, never an internal match or proof auxiliary. `own` resolves the
owner's own data (module, kind); a raw name with no owner in `own`
(should not happen — the owner of an own module's auxiliary is itself an
own declaration) is kept under its own name, unresolved. -/
def ownerSite (own : Std.HashMap String DepConst) (raw : String) : String :=
  ((ownerNames raw).find? own.contains).getD raw

/-- Fold every raw reached name of `reached` to its declaration
(`ownerSite`), keeping the shortest path when two raw names fold to the
same declaration (a declaration and its own generated auxiliary can both
reach the same goal; the declaration's reading is the shorter or equal
path through itself, `docs/decisions.md` D14's rule applied here instead
of at repair time). -/
def foldSites (own : Std.HashMap String DepConst) (reached : Std.HashMap String (List String)) :
    List (String × List String) :=
  let folded := reached.toList.map fun (raw, path) => (ownerSite own raw, path)
  folded.foldl (init := ([] : List (String × List String))) fun acc (site, path) =>
    match acc.findIdx? (·.1 == site) with
    | some i =>
      acc.modify i fun (s, p) => if path.length < p.length then (s, path) else (s, p)
    | none => acc ++ [(site, path)]

/-- `added` with every axiom `decl` already had at the base side removed
(`baseAxioms`, `decl`'s own full axiom set there — empty for a
declaration `baseAxioms` has no entry for, a declaration the bump adds,
which cannot happen under decision D10). An axiom the declaration
already reached through an unrelated path is not a new finding: the
dependency reach is real, but it changes nothing the declaration did
not already have. -/
def newAxioms (baseAxioms : Std.HashMap String (List String)) (decl : String)
    (added : List String) : List String :=
  added.filter (· ∉ baseAxioms.getD decl [])

/-- `removed` restricted to an axiom `decl` had at the base side and does
not have at the after side (`afterAxioms decl`, the declaration's own
`DepConst.axioms`): a dependency constant losing an axiom removes
nothing from `decl`'s own set unless `decl` actually depended on it,
and unless no other path still supplies it at after. -/
def lostAxioms (baseAxioms : Std.HashMap String (List String)) (afterAxioms : List String)
    (decl : String) (removed : List String) : List String :=
  removed.filter fun x => x ∈ baseAxioms.getD decl [] && x ∉ afterAxioms

/-- Whether a dependency-diff entry's own kind carries an axiom change:
`.axioms` (its axiom set differs) or `.onlyAfter` (it is new, its whole
axiom set is a gain). `deepestChange` continues through an entry only
when this holds; `.body` and `.onlyBefore` end a chain. -/
def DepDiffKind.changesAxioms : DepDiffKind → Bool
  | .axioms .. => true
  | .onlyAfter => true
  | _ => false

/-- The axioms one entry itself contributes: `added` for `.axioms` (its
own delta), the whole axiom set for `.onlyAfter` (it is new, so all of
it is a gain). `[]` for any other kind (never read: `deepestChange` only
calls this on an entry `changesAxioms` already holds for). -/
def DepDiffEntry.contributed : DepDiffEntry → List String
  | e => match e.kind with
    | .axioms added _ => added
    | .onlyAfter => (e.after.map (·.const.axioms)).getD []
    | _ => []

/-- Dependency-diff entries by name, for `deepestChange`'s forward walk. -/
def entryIndex (entries : List DepDiffEntry) : Std.HashMap String DepDiffEntry :=
  entries.foldl (fun m e => m.insert e.name e) {}

/-- From `e`, the first dependency entry an own declaration's path
reaches, continue through its after-side `uses` (`docs/static-diff.md`
§ 2) while the immediate next name is itself a changed entry
(`DepDiffKind.changesAxioms`) whose own contribution is a superset of
the current one's (`DepDiffEntry.contributed`): the same direction
`pickCause` already walks within a target's own closure (toward the
axiom, taking the nearest constant that still differs), applied one
layer further out, into the dependencies themselves —
`Lean.instForInLoopUnitOfMonad` (the `ForIn` instance a target's
`for`/`while` reaches directly) uses `Lean.Loop.forIn` directly, both
axioms-changed entries with the identical three-axiom contribution on
EquiVM's pins, so the card names `Lean.Loop.forIn`, the constant nearer
the change's own source, not the instance that merely forwards to it.
The superset requirement stops the walk from wandering into an
unrelated, weaker dependency-diff entry that an entry's `uses` also
happens to reach (a core Lean name the diff flags changed for an
unrelated, smaller reason): a successor must explain at least as much
as the current entry, never less. The candidate is also never the axiom
declaration itself (`kind == "axiom"`): the axiom an entry's own axiom
set gains is trivially "a changed entry that contains itself", which
would make every walk end at the axiom's bare declaration, the thing a
finding's `path` already ends at, never a cause — `pickCause`
(`Core/Cause.lean`) excludes the axiom from its own walk the same way.
Returns the deepest entry reached and the hop names from `e` to it
(not including `e` itself); each dependency name is visited at most
once, so a cycle in `uses` cannot loop forever, and `idx.size + 1`
rounds visit every one. -/
def deepestChange (idx : Std.HashMap String DepDiffEntry) (e : DepDiffEntry) :
    DepDiffEntry × List String :=
  Id.run do
  let mut cur := e
  let mut hops : List String := []
  let mut seen : Std.HashSet String := ({} : Std.HashSet String).insert e.name
  for _ in [0:idx.size + 1] do
    let curSet := cur.contributed
    let uses := (cur.after.map (·.const.uses)).getD []
    let next? := uses.find? fun u =>
      !seen.contains u && match idx[u]? with
        | none => false
        | some e' => e'.kind.changesAxioms && curSet.all (· ∈ e'.contributed) &&
            (e'.after.map (·.const.kind)) != some "axiom"
    match next? with
    | none => break
    | some u =>
      let some e' := idx[u]? | break
      seen := seen.insert u
      hops := hops ++ [u]
      cur := e'
  pure (cur, hops)

/-- Propagation (`docs/static-diff.md` § 2): the predicted findings of a
dependency diff `entries`, through the target's own after-side constant
graph `own` and each own declaration's full axiom set at the base side
(`baseAxioms`, from `export --own` run at the base toolchain — the same
shell call `own` itself came from, at the other side). For each
`axioms`/`onlyAfter` entry, every own declaration whose after-side path
reaches it gets an `AxiomPrediction`, continued to the deepest changed
dependency entry still reachable through the dependency's own `uses`
(`deepestChange`), and whose own axiom set actually changes because of
it (`newAxioms`/`lostAxioms`). For each `body` entry whose own
dependency constant is a `def`, `instance` or `abbrev`, every own
`def`/`instance`/`abbrev` whose path reaches it gets a
`BehaviorPrediction`. An `onlyBefore` entry (a dependency constant
removed at after) cannot be reached by an after-side own declaration,
so it gives no prediction. -/
def propagate (entries : List DepDiffEntry) (own : List DepConst)
    (baseAxioms : Std.HashMap String (List String)) : Predictions := Id.run do
  let idx := ownIndex own
  let rev := reverseUses own
  let bound := own.length + 1
  let depIdx := entryIndex entries
  let mut axioms : List AxiomPrediction := []
  let mut behavior : List BehaviorPrediction := []
  for e in entries do
    if e.kind.changesAxioms then
      let (term, hops) := deepestChange depIdx e
      for (decl, path) in foldSites idx (reachersOf bound rev e.name) do
        if let some oc := idx[decl]? then
          let fullPath := path ++ hops
          match term.kind, term.after with
          | .axioms added removed, after =>
            let causeModule := (after.map (·.const.module)).getD ""
            let axiomsAdded := newAxioms baseAxioms decl added
            let axiomsRemoved := lostAxioms baseAxioms oc.axioms decl removed
            unless axiomsAdded.isEmpty && axiomsRemoved.isEmpty do
              let p : AxiomPrediction :=
                { decl, module := oc.module, axiomsAdded, axiomsRemoved,
                  cause := term.name, causeModule, path := fullPath }
              axioms := axioms ++ [p]
          | .onlyAfter, some a =>
            let axiomsAdded := newAxioms baseAxioms decl a.const.axioms
            unless axiomsAdded.isEmpty do
              let p : AxiomPrediction :=
                { decl, module := oc.module, axiomsAdded, axiomsRemoved := [],
                  cause := term.name, causeModule := a.const.module, path := fullPath }
              axioms := axioms ++ [p]
          | _, _ => pure ()
    match e.kind, e.after with
    | .body, some a =>
      if computes a.const.kind then
        for (decl, path) in foldSites idx (reachersOf bound rev e.name) do
          if let some oc := idx[decl]? then
            if computes oc.kind then
              let p : BehaviorPrediction :=
                { decl, module := oc.module, cause := e.name, causeModule := a.const.module, path }
              behavior := behavior ++ [p]
    | _, _ => pure ()
  let sortedAxioms := (axioms.toArray.qsort (·.decl < ·.decl)).toList
  let sortedBehavior := (behavior.toArray.qsort (·.decl < ·.decl)).toList
  pure { axioms := sortedAxioms, behavior := sortedBehavior }

end LeanMend
