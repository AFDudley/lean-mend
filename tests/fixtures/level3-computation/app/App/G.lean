import Dep

/-! The target. Its source does not change at the bump. `g` reaches the
dependency's `pick` directly, so its axioms change with the dependency.
`g` is a `def`, not a `theorem`: its edit can change what it computes
(decision D16), so acceptance needs the rebuild path, not the walk. It is
`noncomputable` so its source compiles unchanged at both the v1 (plain)
and v2 (classical) `Dep.pick`. -/
namespace App

noncomputable def g : Nat := Dep.pick

end App
