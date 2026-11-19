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

end Dep
