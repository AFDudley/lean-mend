/-! Lean v4.33.1 `simp [Res.bind, bind]` no longer reduces `pure` of a user
monad: it leaves `match pure 0, f with …` and the goal stays unsolved. v4.29.0
reduced it. The shape is EquiVM's `Reasoning.VyperDispatch` 338, where the
monad is `Stele.EvalResult` with `pure := .ok`. -/
namespace App

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

def gt0 (x : Nat) : Res Bool := do
  let y ← lit 0
  .ok (decide (y < x))

theorem gt0_eq (x : Nat) : gt0 x = .ok (decide (0 < x)) := by
  simp [gt0, lit, bind, Res.bind]

end App
