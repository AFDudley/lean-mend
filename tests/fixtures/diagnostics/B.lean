variable {s t : Nat}
inductive R (a : Nat) : Nat → Nat → Prop where
  | mk {s t} : R a s t
