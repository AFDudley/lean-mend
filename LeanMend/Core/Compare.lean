import LeanMend.Spec.Invariant
import Std.Data.HashMap
import Std.Data.HashSet

/-!
# Compare

The `compare` transition: baseline and after certificates to findings. A
finding either needs a card or breaks the invariant. See `docs/machine.md`
§ The invariant and `docs/verification.md` § Cards.

`compare` is the specification: it scans the after certificate and the alias
map once for each baseline declaration. `compareIx` gives the same findings in
the same order from a `CompareIndex`, with one hash lookup per question
(`compareIx_eq`). `RunState.close` runs `compareIx`.
-/

namespace LeanMend

/-- Why a baseline declaration is not `DeclOk`. -/
inductive Reason where
  /-- The declaration's module builds, but the declaration is not in the after
  certificate. lean-mend never deletes a declaration, so this breaks the
  invariant. -/
  | missing
  /-- The statement hash differs. lean-mend cannot edit a statement, so this
  breaks the invariant. -/
  | statementChanged
  /-- The axioms differ and no card accepts it: a Violation card. -/
  | axiomsDiffer
  /-- A definition body changed and no card accepts it: a Behavior card. -/
  | definitionChanged
  deriving DecidableEq, Repr

structure Finding where
  decl : Decl
  reason : Reason
  deriving Repr

/-- The card a finding needs, or `none` when no card can accept it. -/
def Reason.card : Reason → Option CardKind
  | .axiomsDiffer => some .violation
  | .definitionChanged => some .behavior
  | .missing | .statementChanged => none

/-- The reason a declaration fails `DeclOk`. Called only on failing
declarations; the order of the tests gives the most serious reason. -/
def reasonFor (m : AliasMap) (after : Certificate) (js : List Judgment) (b : Decl) :
    Reason :=
  match after.decls.find? (·.name == m.rename b.name) with
  | none => .missing
  | some a =>
    if a.statementHash ≠ b.statementHash ∧ a.name ∉ after.followed then .statementChanged
    else if a.axioms ≠ b.axioms ∧ ¬ accepted js .violation a.name then .axiomsDiffer
    else .definitionChanged

/-- Every baseline declaration that is not `DeclOk`, with its reason. -/
def compare (m : AliasMap) (base after : Certificate) (js : List Judgment) :
    List Finding :=
  (base.decls.filter (fun b => !decide (DeclOk m after js b))).map
    fun b => ⟨b, reasonFor m after js b⟩

/-- `compare` is sound: no finding means no harm. -/
theorem compare_nil (m : AliasMap) (base after : Certificate) (js : List Judgment)
    (h : compare m base after js = []) : NoHarm m base after js := by
  intro b hb
  simp only [compare, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  have := h b hb
  simpa using this

/-- The after certificate and the alias map, indexed by name. -/
structure CompareIndex where
  /-- `AliasMap.rename` as a map: the first pair of each old name. -/
  aliases : Std.HashMap String String
  /-- Every after declaration of each name, in certificate order. -/
  decls : Std.HashMap String (List Decl)
  built : Std.HashSet String
  followed : Std.HashSet String

/-- The first pair of each key wins, as in `List.lookup`. -/
def aliasIndex (m : AliasMap) : Std.HashMap String String :=
  m.pairs.foldr (fun p acc => acc.insert p.1 p.2) ∅

def declIndex (ds : List Decl) : Std.HashMap String (List Decl) :=
  ds.foldr (fun d acc => acc.insert d.name (d :: acc.getD d.name [])) ∅

def nameSet (l : List String) : Std.HashSet String :=
  l.foldr (fun x acc => acc.insert x) ∅

def CompareIndex.of (m : AliasMap) (after : Certificate) : CompareIndex :=
  { aliases := aliasIndex m, decls := declIndex after.decls,
    built := nameSet after.built, followed := nameSet after.followed }

def CompareIndex.rename (ix : CompareIndex) (n : String) : String :=
  ix.aliases[n]?.getD n

/-- The after declarations named `n`. -/
def CompareIndex.named (ix : CompareIndex) (n : String) : List Decl :=
  ix.decls.getD n []

/-- `DeclOk`, decided with the index. -/
def CompareIndex.declOk (ix : CompareIndex) (js : List Judgment) (b : Decl) : Bool :=
  b.kind.isType || !ix.built.contains b.module ||
    (ix.named (ix.rename b.name)).any fun a =>
      (a.statementHash == b.statementHash || ix.followed.contains a.name) &&
      (a.axioms == b.axioms || decide (accepted js .violation a.name)) &&
      (!b.kind.computes || a.bodyHash == b.bodyHash || decide (accepted js .behavior a.name))

/-- `reasonFor`, with the index. -/
def CompareIndex.reason (ix : CompareIndex) (js : List Judgment) (b : Decl) : Reason :=
  match (ix.named (ix.rename b.name)).head? with
  | none => .missing
  | some a =>
    if a.statementHash ≠ b.statementHash ∧ ix.followed.contains a.name = false then
      .statementChanged
    else if a.axioms ≠ b.axioms ∧ ¬ accepted js .violation a.name then .axiomsDiffer
    else .definitionChanged

/-- `compare`, with the index: time linear in the declaration count. -/
def compareIx (ix : CompareIndex) (base : Certificate) (js : List Judgment) : List Finding :=
  (base.decls.filter (fun b => !ix.declOk js b)).map fun b => ⟨b, ix.reason js b⟩

theorem aliasIndex_rename (m : AliasMap) (after : Certificate) (n : String) :
    (CompareIndex.of m after).rename n = m.rename n := by
  suffices h : (aliasIndex m)[n]? = m.pairs.lookup n by
    simp [CompareIndex.rename, CompareIndex.of, AliasMap.rename, h]
  unfold aliasIndex
  induction m.pairs with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨a, b⟩ := p
    rw [List.foldr_cons, Std.HashMap.getElem?_insert, List.lookup_cons, ih]
    by_cases h : a = n
    · subst h; simp
    · have h' : (n == a) = false := by simp [Ne.symm h]
      simp [h, h']

theorem declIndex_named (m : AliasMap) (after : Certificate) (n : String) :
    (CompareIndex.of m after).named n = after.decls.filter (·.name == n) := by
  simp only [CompareIndex.named, CompareIndex.of]
  induction after.decls with
  | nil => simp [declIndex]
  | cons d ds ih =>
    simp only [declIndex, List.foldr_cons, Std.HashMap.getD_insert] at ih ⊢
    by_cases h : d.name = n
    · subst h; simp [ih]
    · simp [h, ih]

theorem nameSet_mem (l : List String) (x : String) : x ∈ nameSet l ↔ x ∈ l := by
  rw [Std.HashSet.mem_iff_contains]
  induction l with
  | nil => simp [nameSet]
  | cons y ys ih =>
    simp only [nameSet, List.foldr_cons, Std.HashSet.contains_insert] at ih ⊢
    rw [Bool.or_eq_true, beq_iff_eq, ih, List.mem_cons, eq_comm]

theorem CompareIndex.declOk_eq (m : AliasMap) (after : Certificate) (js : List Judgment)
    (b : Decl) : (CompareIndex.of m after).declOk js b = decide (DeclOk m after js b) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold CompareIndex.declOk DeclOk
  rw [aliasIndex_rename, declIndex_named]
  simp only [CompareIndex.of]
  cases b.kind.isType <;>
    simp [nameSet_mem, List.any_eq_true, and_assoc, or_assoc, Decidable.imp_iff_not_or]

theorem CompareIndex.reason_eq (m : AliasMap) (after : Certificate) (js : List Judgment)
    (b : Decl) : (CompareIndex.of m after).reason js b = reasonFor m after js b := by
  unfold CompareIndex.reason reasonFor
  rw [aliasIndex_rename, declIndex_named, List.head?_filter]
  simp only [CompareIndex.of]
  split <;> simp [nameSet_mem]

/-- The indexed compare gives the same findings, in the same order. -/
theorem compareIx_eq (m : AliasMap) (base after : Certificate) (js : List Judgment) :
    compareIx (CompareIndex.of m after) base js = compare m base after js := by
  simp only [compareIx, compare, CompareIndex.declOk_eq, CompareIndex.reason_eq]

/-- Types whose text changed, or that are missing, after the run: warnings,
never findings (decision D11). lean-mend changes a type only with
`--annotate-binders`, so a change here is that edit, reported. The lookups use
`CompareIndex`, as `compareIx` does. -/
def typeChanges (m : AliasMap) (base after : Certificate) : List (Decl × String) :=
  let ix := CompareIndex.of m after
  base.decls.filterMap fun b =>
    if !b.kind.isType || !ix.built.contains b.module then none else
    match (ix.named (ix.rename b.name)).head? with
    | none => some (b, "missing")
    | some a => if a.statementHash == b.statementHash then none else some (b, "changed")

end LeanMend
