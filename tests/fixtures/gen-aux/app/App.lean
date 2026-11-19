/-- A many-constructor type, with a `match` that groups most of its
constructors into a few arms and falls back to a wildcard, the shape
`docs/static-diff.md` § 3 names as the sparse-`casesOn` trigger
(`backward.match.sparseCases`): `Lean.Meta.Constructions.SparseCasesOn`
emits `_sparseCasesOn_N` for an inductive this way at both v4.29.0 and
v4.33.1 (measured, `tests/gen-aux.sh`), so that alone is not the EquiVM
E3 difference. This mimics `Stele.Interp.Expr`/`allocationSizes`
(`EquiVM/Stele/Interp.lean`), a `partial def` with grouped OR-pattern
arms over a many-constructor type and a `where`-bound helper, as closely
as a Lean-core-only fixture can. -/
mutual
inductive Expr where
  | newBytes (n : Expr)
  | newArray (ty : Nat) (n : Expr)
  | tupleGet (e : Expr) (i : Nat) | field (e : Expr) (f : Nat) | inRange (lo : Nat) (e : Expr)
    | cast (e : Expr) (ty : Nat) | addrOf (e : Expr) | unary (op : Nat) (e : Expr) | keccak256 (e : Expr)
    | abiDecode (ty : Nat) (e : Expr) | extCodeSize (e : Expr) | blockhash (e : Expr)
    | balanceOf (e : Expr) | extCodeHash (e : Expr)
  | structLit (ty : Nat) (fields : List (Nat × Expr))
  | arrayLit (es : List Expr) | tupleLit (es : List Expr) | abiEncodeCall (sel : Nat) (es : List Expr)
  | abiEncodePacked (es : List (Nat × Expr))
  | bytesSlice (a b c : Expr) | ite (a b c : Expr)
  | binary (op : Nat) (a b : Expr) | index (a b : Expr) | extCodePrefix (a b : Expr)
  | storage (r : Ref) | transient (r : Ref) | arrayLength (ty : Nat) (r : Ref)
  | intLit (n : Nat) | boolLit (b : Bool)
  deriving Inhabited

inductive Ref where
  | mk (base : Nat) (steps : List Step)
  deriving Inhabited

inductive Step where
  | field (i : Nat)
  | mindex (e : Expr)
  | aindex (e : Expr)
  deriving Inhabited
end

def Ref.steps : Ref → List Step
  | .mk _ s => s

partial def allocationSizes : Expr → List Expr
  | .newBytes n => n :: allocationSizes n
  | .newArray _ n => n :: allocationSizes n
  | .tupleGet e _ | .field e _ | .inRange _ e | .cast e _ | .addrOf e | .unary _ e | .keccak256 e
  | .abiDecode _ e | .extCodeSize e | .blockhash e | .balanceOf e | .extCodeHash e => allocationSizes e
  | .structLit _ fields => fields.flatMap fun (_, e) => allocationSizes e
  | .arrayLit es | .tupleLit es | .abiEncodeCall _ es => es.flatMap allocationSizes
  | .abiEncodePacked es => es.flatMap fun (_, e) => allocationSizes e
  | .bytesSlice a b c | .ite a b c => allocationSizes a ++ allocationSizes b ++ allocationSizes c
  | .binary _ a b | .index a b | .extCodePrefix a b => allocationSizes a ++ allocationSizes b
  | .storage r | .transient r | .arrayLength _ r => refExprs r |>.flatMap allocationSizes
  | _ => []
where
  refExprs (r : Ref) : List Expr :=
    r.steps.filterMap fun | .mindex e | .aindex e => some e | .field _ => none

def useRefExprs (r : Ref) : List Expr := allocationSizes.refExprs r
