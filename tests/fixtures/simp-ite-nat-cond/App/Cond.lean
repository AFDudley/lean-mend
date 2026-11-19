/-! `simp [key, h]` unfolds `key` in an `if` condition, but not in the
condition's `Decidable` instance. At v4.29.0 simp closed the goal by
`ite_eq_right_iff`; at v4.33.1 that lemma no longer unifies with the
mismatched instance, and the `if` stays unsolved. The shape is EquiVM's
`Examples.BlindAuction.Bids` 143: a hypothesis `s ≤ i` and a condition
`i < s`. `le_revert` is the same shape with `≤` and `<` swapped. -/
namespace App

inductive R where
  | ok
  | revert

def key (x : Nat) : Nat := x + 1
def len (k : Nat) : Nat := k * 2
def checkLt (i k : Nat) : R := if i < len k then .ok else .revert
def checkLe (i k : Nat) : R := if i ≤ len k then .ok else .revert

theorem lt_revert (i x : Nat) (h : len (x + 1) ≤ i) : checkLt i (key x) = .revert := by
  simp [checkLt, key, h]

theorem le_revert (i x : Nat) (h : len (x + 1) < i) : checkLe i (key x) = .revert := by
  simp [checkLe, key, h]

end App
