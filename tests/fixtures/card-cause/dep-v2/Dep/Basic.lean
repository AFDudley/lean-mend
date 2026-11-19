/-! The dependency at v2. `f_congr` has a proof by contradiction, so it
depends on `Classical.choice` (as Mathlib's `List.find?_congr`, which Mathlib
at Lean v4.33.1 proves with `grind`). `f_pos` moved to `Dep.Pos`. -/
namespace Dep

def f (n : Nat) : Nat := n + 1

theorem f_congr {a b : Nat} (h : a = b) : f a = f b :=
  Classical.byContradiction fun hne => hne (congrArg f h)

end Dep
