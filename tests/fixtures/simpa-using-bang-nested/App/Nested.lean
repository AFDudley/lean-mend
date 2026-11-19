/-! `simpa … using` closes at reducible transparency from Lean v4.31.0
(#13636); v4.29.0 closed at default transparency. Here a `simpa` term holds a
`by simpa` block, and both closes need default transparency: a sum of word
literals (`Word.ofNat 2 + ⟨1⟩`) against one literal (`⟨3⟩`). While the inner
block fails, Lean does not report the outer close. After `using!` on the
inner one alone, Lean reports the outer one at an earlier position, so both
must change in one edit. EquiVM `Examples.OpenZeppelinBench.ERC6909.SetOperator`
44-49 has the same shape. Lean core only. -/
namespace App

structure Word where
  val : Nat

def Word.add (a b : Word) : Word := ⟨a.val + b.val⟩

instance : Add Word := ⟨Word.add⟩

def Word.ofNat (n : Nat) : Word := ⟨n⟩

theorem Word.add_assoc (a b c : Word) : a + b + c = a + (b + c) := by
  show Word.mk (a.val + b.val + c.val) = Word.mk (a.val + (b.val + c.val))
  rw [Nat.add_assoc]

def read (code : List Nat) (pc : Word) : Nat := code.getD pc.val 0

theorem lift {code : List Nat} {pc : Word} (h : read code (pc + ⟨3⟩) = 7) :
    read code (pc + ⟨3⟩) = 7 := h

theorem nested {code : List Nat} {pc : Word} (h : read code (pc + Word.ofNat 2 + ⟨1⟩) = 7) :
    read code (pc + Word.ofNat 2 + ⟨1⟩) = 7 := by
  simpa only [Word.add_assoc]
    using lift (by simpa only [Word.add_assoc] using h)

end App
