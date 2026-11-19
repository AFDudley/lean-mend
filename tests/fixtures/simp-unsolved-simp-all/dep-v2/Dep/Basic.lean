namespace Dep

/-- The word modulus, as EVMLean `UInt256.size`. -/
def size : Nat := 2 ^ 256

instance : NeZero size := ⟨by unfold size; decide⟩

/-- A machine word with the shape of EVMLean `UInt256`. -/
structure W where
  val : Fin size

namespace W
def toNat (w : W) : Nat := w.val.val
instance {n : Nat} : OfNat (Fin size) n := ⟨Fin.ofNat _ n⟩
def ofNat (n : Nat) : W := ⟨Fin.ofNat _ n⟩
end W

/-! v2 adds a simp lemma for a literal `toNat` value, as the EquiVM adopt
commit efbfb862 added `u256_toNat_lit64` to `Reasoning/Solc.lean`. -/
@[simp] theorem toNat_lit64 : (⟨64⟩ : W).toNat = 64 := by decide

end Dep
