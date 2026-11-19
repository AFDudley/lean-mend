import Dep

/-- The target's own declaration: `dep-diff` must not list it; it belongs
to `app`, not to `dep`. -/
def appOwn : Nat := 1

/-- Uses `Dep.f_congr`: the closure from `app`'s own declarations must
reach it. -/
theorem appUsesCongr {a b : Nat} (h : a = b) : Dep.f a = Dep.f b := Dep.f_congr h

/-- Uses `Dep.f_pos`. -/
theorem appUsesPos (n : Nat) : 0 < Dep.f n := Dep.f_pos n

/-- Uses `Dep.usesProof`, an unchanged dependency constant: the diff must
not list it. -/
def appUsesProof (n : Nat) (h : 0 ≤ n) : {m : Nat // 0 ≤ m} := Dep.usesProof n h
