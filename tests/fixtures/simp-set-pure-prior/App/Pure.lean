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

/-! Lean v4.33.1 `simp [gt3, lit, bind, Res.bind]` no longer reduces `pure` of
a user monad: it leaves `match pure 3, f with …`, and `omega` after it cannot
read that goal ("omega could not prove the goal"). v4.29.0 reduced it to
`x ≤ 3`. The shape is EquiVM's `Examples.UniswapV2Pair.MathRoutines` 38 and
169, and `Examples.OpenZeppelinBench.ERC6909.TransferFrom.Common` 500 and 512,
where the monad is `Stele.EvalResult` with `pure := .ok`. -/

inductive Res (α : Type) where
  | ok (a : α)
  | revert

def Res.bind {α β : Type} : Res α → (α → Res β) → Res β
  | .ok a, f => f a
  | .revert, _ => .revert

instance : Monad Res where
  pure := .ok
  bind := Res.bind

def lit (n : Nat) : Res Nat := pure n

def gt3 (x : Nat) : Res Bool := do
  let y ← lit 3
  .ok (decide (y < x))

theorem gt3_false (x : Nat) (h : x ≤ 3) : gt3 x = .ok false := by
  simp [gt3, lit, bind, Res.bind]
  omega

end App
