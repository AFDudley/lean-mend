/-! A fixture for the probe: one of each declaration kind. -/
namespace Fx

def double (n : Nat) : Nat := n + n

abbrev Twice := Nat

instance : Inhabited Twice := ⟨0⟩

def New.f (n : Nat) : Nat := n

@[deprecated New.f (since := "2026-01-01")]
def Old.f := @New.f

inductive Color where
  | red
  | green

class HasZero (α : Type) where
  zero : α

structure Pt where
  x : Nat
  deriving Repr, BEq

theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double; omega

end Fx
