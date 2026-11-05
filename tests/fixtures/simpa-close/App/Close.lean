/-! `simpa … using` closes at reducible transparency from Lean v4.31.0
(#13636); v4.29.0 closed at default transparency. Here the simplified term and
the simplified goal differ in two ways that only default transparency
unfolds: an operation alias (the abbrev `Op.PUSH3` against `Op.Push .PUSH3`)
and a sum of word literals (`Word.ofNat 2 + ⟨1⟩`) against one literal
(`⟨3⟩`). EquiVM `Reasoning.SolcRoutines` 1464 has the same shape. Lean core
only. -/
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

theorem fetch {code : List Nat} {pc : Word}
    (_ : decode code (pc + Word.ofNat 2 + ⟨1⟩) = some (.Push .PUSH3, some (⟨7⟩, 3))) : True :=
  trivial

theorem step {code : List Nat} {pc : Word} (hwf : Wf code pc) :
    decode code (pc + Word.ofNat 2 + ⟨1⟩) = some (.Push .PUSH3, some (⟨7⟩, 3)) := by
  simpa only [Word.add_assoc] using hwf.d3

theorem inTerm {code : List Nat} {pc : Word} (hwf : Wf code pc) : True :=
  fetch (by simpa only [Word.add_assoc] using hwf.d3)

end App
