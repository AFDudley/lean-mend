/-! The app of tests/cert-generated.sh. The bump commit changes only the
toolchain, from v4.29.0 to v4.33.1. The `deriving` clauses make constants
that only the compiler declares. At v4.29.0, `deriving Inhabited` on
`Pools` also makes `App.instInhabitedPools.default`, with a declaration
range inside the `structure` command. At v4.33.1 that constant has no
declaration range. EquiVM run 9 halted with `invariantBroken` on this
shape (`Stele.DiffTest.Pools`).

The unnamed instances below get a name from Lean. The name is the same at
v4.29.0 and v4.33.1 (docs/verification.md § The certificate). -/
namespace App

/-- The shape of `Stele.DiffTest.Pools`: fields with default values and
`deriving Inhabited` on a line of its own. -/
structure Pools where
  words : List Nat := []
  bytes : List UInt8 := []
  deriving Inhabited

-- A core class applied to a structure, with a `where` body. It follows
-- `Pools` at once, as `instance : Append Pools` follows `Pools` in
-- `Stele/DiffTest/Gen.lean`.
instance : Append Pools where
  append a b := { words := a.words ++ b.words, bytes := a.bytes ++ b.bytes }

structure Stats where
  hits : Nat
  misses : Nat
  deriving Repr, BEq

inductive Color where
  | red | green
  deriving BEq, Repr, DecidableEq

class Size (α : Type) where
  size : α → Nat

-- A user class applied to a structure.
instance : Size Pools := ⟨fun p => p.words.length⟩

-- Dependent instances.
instance [Size α] : Size (List α) := ⟨fun l => l.length⟩
instance {n : Nat} : Size (Fin n) := ⟨fun i => i.val⟩
instance (n : Nat) : OfNat Pools n := ⟨⟨[n], []⟩⟩

-- A class with two arguments.
instance : HAdd Pools Nat Pools := ⟨fun p n => { p with words := n :: p.words }⟩

theorem pools_words : (default : Pools).words = [] := rfl

end App
