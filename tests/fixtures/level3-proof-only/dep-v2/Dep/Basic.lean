/-! The dependency at v2. `lem` now has a proof by contradiction, so it
depends on `Classical.choice` (as Mathlib's `List.find?_congr`, which
Mathlib at Lean v4.33.1 proves with `grind`). `lemC` is the same statement,
with the v1 constructive proof, under a new name: the shape `replaceInBody`
targets (`docs/rules.md` § Edit operations). -/
namespace Dep

theorem lem : (1 : Nat) + 1 = 2 := Classical.byContradiction fun h => h rfl

theorem lemC : (1 : Nat) + 1 = 2 := rfl

end Dep
