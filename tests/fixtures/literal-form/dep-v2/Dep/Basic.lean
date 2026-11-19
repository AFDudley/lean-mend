namespace Dep

/-- The word modulus, as EVMLean `UInt256.size`. -/
def size : Nat := 2 ^ 256

instance : NeZero size := ⟨by unfold size; decide⟩

/-- A machine word with the shape of EVMLean `UInt256`. -/
structure W where
  val : Fin size
  deriving DecidableEq

namespace W
def toNat (w : W) : Nat := w.val.val
instance {n : Nat} : OfNat (Fin size) n := ⟨Fin.ofNat _ n⟩
/-- As EVMLean `UInt256.ofNat`: a literal `W.ofNat n` and `⟨n⟩` are equal only
after `W.ofNat` unfolds, so not at reducible transparency. -/
def ofNat (n : Nat) : W := Id.run do ⟨Fin.ofNat _ n⟩
def add (a b : W) : W := ⟨a.val + b.val⟩
instance : Add W := ⟨add⟩
def gt (a b : W) : W := if a.val > b.val then ⟨1⟩ else ⟨0⟩
end W

/-! v2 adds simp lemmas for literal `toNat` values, as the EquiVM adopt commit
efbfb862 added `u256_toNat_lit{0,1,4,32,64,128,160}` to `Reasoning/Solc.lean`. -/
@[simp] theorem toNat_lit32 : (⟨32⟩ : W).toNat = 32 := by decide
@[simp] theorem toNat_lit160 : (⟨160⟩ : W).toNat = 160 := by decide

end Dep
