import Dep

/-! The target. Its source does not change at the bump. Its theorems reach
the dependency's lemmas, so their axioms change with the dependency:
`mid`, `t1` and `t2` through `Dep.f_congr`, `t3` through `Dep.f_pos`. -/
namespace App

theorem mid (a b : Nat) (h : a = b) : Dep.f a = Dep.f b := Dep.f_congr h

theorem t1 (a : Nat) : Dep.f a = Dep.f (a + 0) := mid a (a + 0) rfl

theorem t2 (a : Nat) : Dep.f (a + 0) = Dep.f a := mid (a + 0) a rfl

theorem t3 (n : Nat) : 0 < Dep.f n := Dep.f_pos n

end App
