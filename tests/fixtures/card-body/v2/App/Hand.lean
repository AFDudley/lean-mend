/-! Two definitions that the bump commit itself changes, as the bump commit
of EquiVM run 10 held the repairs of run 9 (`EVM.Word.toBytesLEWithSizeProof`).
No commit of the run touches this module. -/
namespace App

/-- The bump commit writes the proof in term mode. -/
def sized (n : Nat) : {m : Nat // m ≤ n + 1} := ⟨n, Nat.le_succ n⟩

/-- The bump commit changes the number that this `by` block computes. -/
def count : Nat := by exact 3

end App
