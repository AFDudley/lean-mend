/-! Unnamed instances of many shapes, for tests/cert-generated.sh. Lean gives
each one a name. The certificate keys an unnamed instance by that name, so
the name must be the same at v4.29.0 and at v4.33.1. It is, for every shape
here (docs/verification.md § The certificate, the table of names). The
names are in the comment above each instance. -/
namespace App.Inst

class Size (α : Type) where
  size : α → Nat

class Pos (α : Type) where
  val : α → Nat
  pos : ∀ a, 0 < val a + 1

structure Pools where
  words : List Nat := []

structure Box (α : Type) where
  val : α

inductive Tree where
  | leaf
  | node (l r : Tree)

def IsEven (n : Nat) : Prop := n % 2 = 0

-- instSizeBox: a dependent instance on a structure with a parameter.
instance [Size α] : Size (Box α) := ⟨fun b => Size.size b.val⟩
-- instCoeNatPools
instance : Coe Nat Pools := ⟨fun n => ⟨[n]⟩⟩
-- instSizeForallNat: a function type.
instance : Size (Nat → Nat) := ⟨fun _ => 0⟩
-- instSizeProdNatPools: a product.
instance : Size (Nat × Pools) := ⟨fun _ => 0⟩
-- instDecidablePredNatIsEven
instance : DecidablePred IsEven := fun n => inferInstanceAs (Decidable (n % 2 = 0))
-- instDecidableIsEven
instance (n : Nat) : Decidable (IsEven n) := inferInstanceAs (Decidable (n % 2 = 0))
-- instDecidableLtOfNat_app: a proposition with literals.
instance : Decidable (1 < 2) := isTrue (by decide)
-- instFunctorBox: a class on a type constructor.
instance : Functor Box := ⟨fun f b => ⟨f b.val⟩, fun a _ => ⟨a⟩⟩
-- instInhabitedPools: a priority.
instance (priority := low) : Inhabited Pools := ⟨{}⟩
-- instSizeBool: an attribute.
@[reducible] instance : Size Bool := ⟨fun _ => 1⟩
-- instToStringPools: a `where` body.
instance : ToString Pools where
  toString p := toString p.words
-- instReprBoxNat: a class applied to an applied type.
instance : Repr (Box Nat) := ⟨fun b _ => repr b.val⟩
-- instSizeTree: a field that a `where` function defines. Lean also makes
-- `App.Inst.instSizeTree.go`, which has no row.
instance : Size Tree where
  size := go
where
  go : Tree → Nat
    | .leaf => 1
    | .node l r => go l + go r
-- instPosPools: a proof field.
instance : Pos Pools where
  val p := p.words.length
  pos _ := by omega
-- instCommutativeNatHAdd_app: an instance of a class in `Prop`.
instance : Std.Commutative (α := Nat) (· + ·) := ⟨Nat.add_comm⟩
-- instInhabitedForallNat_app
instance : Inhabited (Nat → Nat) := ⟨id⟩

section
variable {α : Type} [Pos α]
-- instPosOption: a `variable` of the section.
instance : Pos (Option α) where
  val | none => 0 | some a => Pos.val a
  pos _ := Nat.succ_pos _
end

end App.Inst

-- instSizeString: outside a namespace.
instance : App.Inst.Size String := ⟨String.length⟩
