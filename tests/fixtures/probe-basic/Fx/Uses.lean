import Fx.Basic

namespace Fx

theorem em_use (p : Prop) : p ∨ ¬p := Classical.em p

theorem double_zero : double 0 = 0 := rfl

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

/-- An axiom: its statement is its signature, its body is empty. -/
axiom zero_eq_zero : (0 : Nat) = 0

/-- A declaration outside the namespace: the name is `fx_true`. -/
theorem _root_.fx_true : True := trivial

/-- A command macro that makes a theorem, as Mathlib's `lemma`: Lean's
declaration range starts at the `fx_lemma` command. -/
macro "fx_lemma " id:declId sig:declSig val:declVal : command => `(theorem $id $sig $val)

fx_lemma double_one : double 1 = 2 := rfl

end Fx
