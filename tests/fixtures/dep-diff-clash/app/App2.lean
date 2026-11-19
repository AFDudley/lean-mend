import Dep

/-- The same literal top-level name `App.lean` declares. -/
def main : IO UInt32 := pure 1

/-- Uses `Dep.f_pos`: the union of the recovered export calls must reach
it too, from the other side of the clash. -/
theorem appUsesPos (n : Nat) : 0 < Dep.f n := Dep.f_pos n
