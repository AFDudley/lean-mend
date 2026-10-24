import Dep

/-! Proofs that a change of the dependency's simp set breaks. -/
namespace App

open Dep

theorem a1 : foo + 1 = 2 := by
  simp

theorem a2 (P : Nat → Prop) (h : P foo) : P 1 := by
  simpa using h

theorem a3 : bar = 2 := by
  try simp
  rfl

end App
