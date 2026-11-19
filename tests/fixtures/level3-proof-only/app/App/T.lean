import Dep

/-! The target. Its source does not change at the bump. `t` reaches the
dependency's `lem` directly, so its axioms change with the dependency. -/
namespace App

theorem t : (1 : Nat) + 1 = 2 := Dep.lem

end App
