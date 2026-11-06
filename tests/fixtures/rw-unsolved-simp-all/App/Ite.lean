/-! EquiVM `Examples/UniswapV2Pair/ConstructorDomainSource.lean` 27. `simp only`
unfolds `Fin.toNat` and `bound` in the `if` condition, but not in its
`Decidable` instance. Lean v4.33.1 then finds the term "not type-correct under
the `implicit` transparency level", and `if_pos h` no longer rewrites the `if`.
v4.29.0 rewrote it. The `rw` after it leaves the `if` in the goal. `and_true`
makes the proof depend on `propext` before the bump, so `simp_all` changes
no axiom. The repaired EquiVM proof depends on `propext`, `Classical.choice`
and `Quot.sound`. -/
namespace App

def bound : {m : Nat // 0 < m} := ⟨256, by decide⟩

def twoPow (n : Nat) : Nat := 2 ^ n

def cast (x : Fin 300) : Option Nat :=
  if x.toNat < twoPow bound.val then some x.toNat else none

def res (o : Option Nat) : Nat :=
  match o with
  | some a => a
  | none => 0

theorem res_cast (x : Fin 300) (h : x.val < twoPow 256) : res (cast x) + 0 = x.val ∧ True := by
  simp only [res, cast, bound, Fin.toNat, if_pos h, and_true]
  rw [Nat.add_zero]

end App
