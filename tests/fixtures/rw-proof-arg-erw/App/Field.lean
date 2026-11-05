/-! A lemma takes a proof argument `{h : …}` for a structure's proof field,
with a type that is definitionally equal to the field's type, not the same.
At v4.33.1 `rw [load_01 s]` no longer assigns the target's proof to that
argument, and reports `Did not find an occurrence of the pattern`; v4.29.0
did. The shape is EquiVM's `storageLocLoad_bool_offset0'` and its `hbound`
argument, used at `Examples.Ballot.GiveRightToVote` 250, 270 and
`Examples.Ballot.Voters` 123. -/
namespace App

structure W where
  val : Fin 1024

def W.toNat (w : W) : Nat := w.val.val

structure Loc where
  slot : Nat
  off : Fin 32
  size : Fin 33
  hbound : off.val + size.val - 1 < 32

def load (l : Loc) : Nat := l.slot + l.off.val + l.size.val

theorem load_01 (s : Nat) {h : (⟨0⟩ : W).toNat + (⟨1⟩ : W).toNat ≤ 32} :
    load { slot := s, off := 0, size := 1, hbound := h } = s + 1 := by
  simp [load]

def layout : Loc := { slot := 5, off := 0, size := 1, hbound := by decide }

theorem load_inline (s : Nat) :
    load { slot := s, off := 0, size := 1, hbound := by decide } = s + 1 := by
  rw [load_01 s]

theorem load_layout : load layout = 6 := by
  change load { slot := 5, off := 0, size := 1, hbound := _ } = 6
  rw [load_01 5]

end App
