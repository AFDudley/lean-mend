/-! Lean v4.33.1 `simp only [bind]` no longer reduces `pure` of a user monad:
it leaves `match pure 0, f with …`. The `simpa` after it then fails with
"Type mismatch: After simplification": the term is `0 < x`, the goal still
holds the `match`. v4.29.0 reduced it. The shape is EquiVM's
`Examples.UniswapV2Pair.UpdateSource` 131, where the monad is
`Stele.EvalResult` with `pure := .ok`. -/
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

def gt0 (x : Nat) : Res Bool := do
  let y ← pure 0
  .ok (decide (y < x))

theorem gt0_true (x : Nat) (h : 0 < x) : gt0 x = .ok true := by
  simp only [gt0, bind]
  simpa [Res.bind] using h

end App
