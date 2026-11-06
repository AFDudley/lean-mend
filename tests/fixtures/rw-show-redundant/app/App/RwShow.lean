import Dep

/-! EquiVM `Examples/BlindAuction/Reveal/Common.lean` 2814 and 2822. With dep
v2, `simp [M]` already rewrites `(⟨32⟩ : W).toNat` and `(⟨64⟩ : W).toNat`, so
the `rw` of the `show` term finds nothing. The `rw [h]` after it still applies. -/
namespace App

open Dep

def M (s a b : Nat) : Nat := s + a + b

theorem rwShow32 (s : Nat) (f : Nat → Nat) (h : f (s + 32 + 32) = s) :
    f (M s (⟨32⟩ : W).toNat 32) = s := by
  simp [M]
  rw [show (⟨32⟩ : W).toNat = 32 by decide]
  rw [h]

theorem rwShow64 (s : Nat) (f : Nat → Nat) (h : f (s + 64) = s) :
    f (M s 0 (⟨64⟩ : W).toNat) = s := by
  simp [M]
  rw [show (⟨64⟩ : W).toNat = 64 from by decide]
  rw [h]

end App
