/-! Lean v4.33.1 `simp only [bind, Option.bind]` no longer reduces `pure x`:
it leaves `match pure x, f with | none, _ => none | some a, f => f a`. A later
tactic then fails on that term. v4.29.0 reduced it. The two shapes are EquiVM's
`Reasoning.TransientPackedStorage` 59 (`apply` could not unify) and
`Reasoning.SteleArithmetic` 223 (`rw [if_neg]` did not find the `if`). -/
namespace App

def toWord (x : Nat) : Option Nat := pure (x % 7)

def store (x : Nat) : Option Nat := do
  let w ← toWord x
  some (w + 1)

theorem store_eq (x : Nat) : store x = some (1 + x % 7) := by
  unfold store
  simp only [toWord, bind, Option.bind]
  congr 1
  apply Nat.add_comm

def check (x : Nat) : Option Nat := do
  let w ← toWord x
  if w < 7 then some w else none

theorem check_eq (x : Nat) : check x = some (x % 7) := by
  unfold check
  simp only [toWord, bind, Option.bind]
  rw [if_pos (Nat.mod_lt x (by decide))]

end App
