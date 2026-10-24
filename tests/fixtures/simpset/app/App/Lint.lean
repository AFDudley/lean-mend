import Dep

/-! The only candidate that repairs `a4` keeps an argument that never
rewrites, so Lean's `linter.unusedSimpArgs` flags the repaired tactic, and
the linter condition must reject it (`docs/machine.md`, accept). -/
namespace App

open Dep

theorem a4 : foo = 1 := by
  simp [Nat.add_zero]

end App
