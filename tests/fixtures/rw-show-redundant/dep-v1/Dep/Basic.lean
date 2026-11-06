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
end W

end Dep
