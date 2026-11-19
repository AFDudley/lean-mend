import Dep

/-! EquiVM `Examples/SimpleAuction/Withdraw.lean` 2070. With dep v2, `simp`
already rewrites `(⟨32⟩ : W).toNat`, so the first `rw` rule finds nothing. -/
namespace App

open Dep

def M (s a b : Nat) : Nat := s + a + b

theorem rwNotFound (s : Nat) (f : Nat → Nat) (h : f (s + 32 + 32) = s) :
    f (M s (⟨32⟩ : W).toNat 32) = s := by
  simp [M]
  rw [show (⟨32⟩ : W).toNat = 32 from by decide,
    h]

end App
