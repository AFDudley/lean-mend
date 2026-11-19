import Dep

/-! EquiVM `Examples/TinyImmutable/Constructor.lean` 934. With dep v2, `simp`
closes the goal, so the `rw` after it has no goal. -/
namespace App

open Dep

theorem rwNoGoals : (⟨160⟩ : W).toNat + 0 = 160 := by
  simp
  rw [show (⟨160⟩ : W).toNat = 160 from by decide]

end App
