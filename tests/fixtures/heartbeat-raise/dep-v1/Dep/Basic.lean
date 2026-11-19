namespace Dep

/-- A recursive definition that `simp` unfolds one step at a time. -/
def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n + 1

/-- The depth of the unfolding. -/
def n : Nat := 500

end Dep
