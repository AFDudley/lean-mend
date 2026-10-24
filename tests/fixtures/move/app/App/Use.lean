import Dep

/-! The dependency moves `Old.Map` to `New.Map` with no aliases. The app uses
the old name in a statement and a proof, and declares a function under the
moved namespace itself, as EVMLean's Conform/Wheels.lean declares
`Batteries.RBMap.partition`. -/
def Old.Map.double (n : Nat) : Nat := Old.Map.size n + Old.Map.size n

theorem size_id (n : Nat) : Old.Map.size n = n := by
  unfold Old.Map.size
  rfl
