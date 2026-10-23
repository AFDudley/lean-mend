import LeanMend.Spec.Invariant

/-!
# Compare

The `compare` transition: baseline and after certificates to findings. A
finding either needs a card or breaks the invariant. See `docs/machine.md`
§ The invariant and `docs/verification.md` § Cards.
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
    if a.statementHash ≠ b.statementHash then .statementChanged
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

end LeanMend
