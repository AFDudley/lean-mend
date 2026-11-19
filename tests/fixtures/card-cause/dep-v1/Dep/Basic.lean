/-! The dependency at v1. Both lemmas have direct proofs, with no axiom. -/
namespace Dep

def f (n : Nat) : Nat := n + 1

theorem f_congr {a b : Nat} (h : a = b) : f a = f b := congrArg f h

/-- In `Dep.Basic` at v1. v2 moves it to `Dep.Pos`. -/
theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n

end Dep
