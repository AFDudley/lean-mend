import Dep

/-! EquiVM `Examples/StringStoreLite/Getters.lean` 3314. With dep v2, `simp`
rewrites the right side to `160`; after the `rw` the two sides differ only by
the literal form `{ val := 160 }.toNat` against `160`. -/
namespace App

open Dep

theorem rwUnsolved (f : Nat → Nat) :
    f ((⟨32⟩ : W) + ⟨128⟩).toNat = f (⟨160⟩ : W).toNat + 0 := by
  simp
  rw [show ((⟨32⟩ : W) + ⟨128⟩).toNat =
      (⟨160⟩ : W).toNat by native_decide]

end App
