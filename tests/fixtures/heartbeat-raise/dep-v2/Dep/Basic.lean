namespace Dep

/-- A recursive definition that `simp` unfolds one step at a time. -/
def f : Nat → Nat
  | 0 => 0
  | n + 1 => f n + 1

/-- The depth of the unfolding. v2 makes it deeper, so the `simp` that unfolds
it costs more heartbeats, as the EquiVM simp at
`Examples/UniswapV2Pair/PermitDecode.lean` 97 did at v4.33.1. -/
def n : Nat := 3000

end Dep
