import LeanMend.Core.Cause
import Std.Data.HashMap

/-!
# The dependency diff (`docs/static-diff.md` § 1, decision S2)

A bump moves a target from toolchain A to toolchain B. Most of the finding
is knowable before any repair runs: a declaration of Lean core, Std,
Batteries, Mathlib or another dependency changed its axiom set or its
proof-erased body between the two pins, and the target inherits the change
through the constants it uses. The dependency diff is the first half of
that prediction (`docs/static-diff.md` § 1): the set of dependency
constants that changed, computed once per pair of pins, independent of any
target. § 2 (propagation through a target's constant graph) is not built
yet.

This module is the pure Core half: it takes each side's rows, already
parsed by the shell from the probe's `export` command
(`LeanMend.Shell.DepDiff`), and computes the diff with no IO. The shell
gathers the rows and resolves each one's owner the way card-cause does
(`LeanMend.Shell.Cause.ownerOfOlean`).
-/

namespace LeanMend

/-- One constant of a dependency, as the probe's `export` command reports
it (`probe/Probe.lean`, `cmdExport`): its kind (`kindOf`), its axiom set,
the immediate constants it uses (`axEdges`, one hop — `docs/static-diff.md`
§ 2, propagation continues past the first changed dependency constant to
the deepest one still reachable by a changed entry, the same rule
`pickCause` already applies within a target's own closure, here applied
one layer out into the dependencies), and a hash of its proof-erased
body (`erasedBody`, `--closure` mode hashes it rather than keeping the
full term: `docs/static-diff.md` § Cost) — `none` for a constant with no
value (an `axiom`, or the type of an `inductive`, `structure` or
`class`). Two export runs, one per toolchain, give a comparable
`bodyHash` for an unchanged constant (`erasedBody`'s doc comment states
why), so a plain string equality on `bodyHash` is the body-changed test,
except for a `theorem`: proof irrelevance (`docs/decisions.md` D16)
means its axiom set is the only comparable fact, so `depDiff` never
reads its `bodyHash` either. -/
structure DepConst where
  name : String
  module : String
  kind : String
  axioms : List String
  uses : List String
  bodyHash : Option String
  deriving Repr, DecidableEq

/-- Constants by name. The same row type serves the target's own
constants (`export --own` for propagation, with `bodyHash := none`;
`export --ownClosure` for generated auxiliaries) and the dependency
constants: one type for one row shape. -/
def ownIndex (cs : List DepConst) : Std.HashMap String DepConst :=
  cs.foldl (fun m c => m.insert c.name c) {}

/-- `DepConst` plus the package and revision of its module at one side
(`Owner`, `LeanMend.Core.Cause`): the same owner computation card-cause
uses on an `explain` row. -/
structure DepRow where
  const : DepConst
  owner : Owner
  deriving Repr, DecidableEq

/-- The rows of one side, by constant name. A later row of the same name
replaces an earlier one; the shell gives one row per constant. -/
def depIndex (rows : List DepRow) : Std.HashMap String DepRow :=
  rows.foldl (fun m r => m.insert r.const.name r) {}

/-- What changed about one dependency constant between the before side (the
old toolchain) and the after side (the new one). -/
inductive DepDiffKind where
  /-- The axiom set differs: the axioms the after side has that the before
  side does not, and the axioms the before side has that the after side
  dropped. -/
  | axioms (added removed : List String)
  /-- The axiom set is the same; the proof-erased body differs. -/
  | body
  /-- The constant exists at the before side only. -/
  | onlyBefore
  /-- The constant exists at the after side only. -/
  | onlyAfter
  deriving Repr, DecidableEq

/-- One entry of the dependency diff (`docs/static-diff.md` § 1): a
constant whose axiom set or proof-erased body differs between the two
sides, or that exists at one side only, with its row at each side where it
exists. -/
structure DepDiffEntry where
  name : String
  kind : DepDiffKind
  before : Option DepRow
  after : Option DepRow
  deriving Repr, DecidableEq

/-- The dependency diff (`docs/static-diff.md` § 1, decision S2): pure over
the two sides' rows, independent of any target. A constant present at both
sides with the same axiom set and the same proof-erased body is not an
entry — most of Lean core and Mathlib does not change between two pins, and
run 10's own dependency diff (`docs/static-diff.md` § 1) has exactly two
entries, `List.find?_congr` (an axiom gain) and `Lean.Loop.forIn` (an axiom
gain), out of the whole closure. An axiom-set change wins over a body
change when both differ: the axiom set is the signal a Violation finding
needs (`docs/static-diff.md` § 1), and a changed proof can change the
proof-erased body (it is erased to the same placeholder, `erasedBody`'s doc
comment) only when the axiom set also changes, so the two cases do not
overlap on a real pair. -/
def depDiff (before after : List DepRow) : List DepDiffEntry :=
  let bIdx := depIndex before
  let aIdx := depIndex after
  let names := (before.map (·.const.name) ++ after.map (·.const.name)).eraseDups
  names.filterMap fun n =>
    match bIdx[n]?, aIdx[n]? with
    | some b, some a =>
      if b.const.axioms != a.const.axioms then
        some { name := n,
               kind := .axioms (a.const.axioms.filter (· ∉ b.const.axioms))
                                (b.const.axioms.filter (· ∉ a.const.axioms)),
               before := some b, after := some a }
      else if b.const.kind == "theorem" && a.const.kind == "theorem" then none
      else if b.const.bodyHash != a.const.bodyHash then
        some { name := n, kind := .body, before := some b, after := some a }
      else none
    | some b, none => some { name := n, kind := .onlyBefore, before := some b, after := none }
    | none, some a => some { name := n, kind := .onlyAfter, before := none, after := some a }
    | none, none => none

end LeanMend
