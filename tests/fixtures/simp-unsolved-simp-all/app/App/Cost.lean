import Dep

/-! EquiVM `Examples/UniswapV2Pair/SkimSafeTransferReturn.lean` 58, 67, 396,
407. The hypothesis `h` has `(⟨64⟩ : W).toNat` inside. With dep v2, `simp`
first rewrites that literal in the goal to `64` (the new simp lemma
`toNat_lit64`), so `h` no longer matches and the goal stays open. -/
namespace App

open Dep

/-- The memory-size function, as EVMLean `MachineState.M`. -/
def M (s f l : Nat) : Nat :=
  match l with
  | 0 => s
  | l => max s ((f + l + 31) / 32)

/-- The memory cost, as EquiVM `Cₘ`. -/
def C (w : W) : Nat := w.toNat * 3

theorem cost (g : W) (h : W.ofNat (M g.toNat (⟨64⟩ : W).toNat 32) = g) :
    C (W.ofNat (M g.toNat (⟨64⟩ : W).toNat 32)) - C g = 0 := by
  simp [h]

end App
