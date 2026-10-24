/-! A constructor binder that repeats a section variable: v4.29.0 accepts it,
v4.33.1 rejects it (decision D11). -/
namespace App

variable {s t : Nat}

inductive R (a : Nat) : Nat → Nat → Prop where
  | mk {s t} : R a s t
  | step {s t} : R a s t → R a t s

theorem r0 : R 0 1 2 := R.mk

end App
