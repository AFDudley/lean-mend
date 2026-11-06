-- `omega` with a goal it cannot read: an opaque `Option` value.
example (n : Nat) (h : n ≤ 3) : (some n).isSome = (n < 4 : Bool) := by
  omega
