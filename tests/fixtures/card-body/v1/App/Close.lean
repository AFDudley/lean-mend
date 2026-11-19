/-! A definition whose body holds a proof that the bump breaks. The types are
those of `tests/fixtures/simpa-close`: from Lean v4.31.0 (#13636)
`simpa … using` closes at reducible transparency, so the proof of the
subtype's property fails at v4.33.1, and the rule `simpa-close-transparency`
repairs it with `using!`. The repair changes a proof only. Lean core only. -/
namespace App

structure Word where
  val : Nat

def Word.add (a b : Word) : Word := ⟨a.val + b.val⟩

instance : Add Word := ⟨Word.add⟩

def Word.ofNat (n : Nat) : Word := ⟨n⟩

theorem Word.add_assoc (a b c : Word) : a + b + c = a + (b + c) := by
  show Word.mk (a.val + b.val + c.val) = Word.mk (a.val + (b.val + c.val))
  rw [Nat.add_assoc]

inductive POp where
  | PUSH1
  | PUSH3

inductive Op where
  | Push : POp → Op
  | STOP

abbrev Op.PUSH3 : Op := .Push .PUSH3

def decode (code : List Nat) (pc : Word) : Option (Op × Option (Word × Nat)) :=
  if pc.val < code.length then some (.Push .PUSH3, some (⟨7⟩, 3)) else none

structure Wf (code : List Nat) (pc : Word) : Prop where
  d3 : decode code (pc + ⟨3⟩) = some (.PUSH3, some (⟨7⟩, 3))

/-- The decoded operation at `pc + 3`, with the proof that `decode` gives it. -/
def checked {code : List Nat} {pc : Word} (hwf : Wf code pc) :
    {o : Option (Op × Option (Word × Nat)) // decode code (pc + Word.ofNat 2 + ⟨1⟩) = o} :=
  ⟨some (.Push .PUSH3, some (⟨7⟩, 3)), by simpa only [Word.add_assoc] using hwf.d3⟩

end App
