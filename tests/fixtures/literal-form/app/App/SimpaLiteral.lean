import Dep

/-! EquiVM `Tests/Pipeline/Vault/Dispatch.lean` 270. Lean v4.33.1 `simpa … using`
compares the simplified term with the goal at reducible transparency; v4.29.0
compared them at default transparency. `{ val := 7 }` and `W.ofNat 7` are
equal only after `W.ofNat` unfolds. The term holds `native_decide`, so a
candidate that keeps it must still pass the clean check. -/
namespace App

open Dep

theorem simpaLiteral (x : W) (hx : x = ⟨5⟩) : W.gt (W.ofNat 7) x ≠ W.ofNat 0 := by
  simpa using (show W.gt ⟨7⟩ x ≠ ⟨0⟩ by rw [hx]; native_decide)

end App
