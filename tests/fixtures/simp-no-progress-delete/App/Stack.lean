/-! EquiVM `Tests/Pipeline/VyperVault/Balances.lean` 89. `step2` takes its
stack as `x0 :: R`, so the unifier unfolds `stk`, and `stk` is not in `h3`.
Lean v4.29.0 accepts `simp only [stk] at h3` with an unused-argument
warning. Lean v4.33.1 reports `` `simp` made no progress ``. -/
namespace App

def P (l : List Nat) : Prop := l.length > 0

/-- A named final stack, as the RD block generator writes them. -/
def stk {x : Nat} {R : List Nat} : List Nat := (x + 1) :: R

theorem step1 {x : Nat} {R : List Nat} (_h : P R) : P (stk (x := x) (R := R)) := by
  simp [P, stk]

theorem step2 {x0 : Nat} {R : List Nat} (_hs : R.length + 3 ≤ 1024) (_h : P (x0 :: R)) :
    P (x0 :: x0 :: R) := by
  simp [P]

theorem twice (R : List Nat) (hR : R.length = 0) (h : P R) : P (4 :: 4 :: R) := by
  have h2 := step1 (x := 3) h
  have h3 := step2 (by simp [hR]) h2
  simp only [stk] at h3
  exact h3

theorem twice' (R : List Nat) (hR : R.length = 1) (h : P R) : P (8 :: 8 :: R) := by
  have h2 := step1 (x := 7) h
  have h3 := step2 (by simp [hR]) h2
  simp only [stk] at h3
  exact h3

end App
