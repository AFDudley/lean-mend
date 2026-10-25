import LeanMend.Spec.Types

/-!
# The invariant

The one invariant, stated before any transition (concept B3). See
`docs/machine.md` § The invariant. This module imports no transition.
-/

namespace LeanMend

/-- A closed card accepts a change of `kind` to `subject`. -/
def accepted (js : List Judgment) (kind : CardKind) (subject : String) : Prop :=
  ∃ j ∈ js, j.kind = kind ∧ j.subject = subject ∧ j.answer = .accept

instance (js : List Judgment) (kind : CardKind) (subject : String) :
    Decidable (accepted js kind subject) := by
  unfold accepted; infer_instance

/-- One baseline declaration is not harmed by the after state. -/
def DeclOk (m : AliasMap) (after : Certificate) (js : List Judgment) (b : Decl) :
    Prop :=
  -- A type's change is a warning, not a breach (decision D11, `typeChanges`).
  b.kind.isType = false →
  b.module ∈ after.built →
    ∃ a ∈ after.decls,
      a.name = m.rename b.name ∧
      -- part 1: the statement is unchanged, or lean-mend changed it to follow
      -- a definition change under --follow-definition-changes (decision D12)
      (a.statementHash = b.statementHash ∨ a.name ∈ after.followed) ∧
      -- part 2: the axioms are unchanged, or a card accepts the difference
      (a.axioms = b.axioms ∨ accepted js .violation a.name) ∧
      -- part 3: a changed definition body needs a card
      (b.kind.computes = false ∨ a.bodyHash = b.bodyHash ∨ accepted js .behavior a.name)

instance (m : AliasMap) (after : Certificate) (js : List Judgment) (b : Decl) :
    Decidable (DeclOk m after js b) := by
  unfold DeclOk; infer_instance

/-- **No harm.** Parts 1 to 3 of the invariant, for every baseline declaration
whose module is built after the run. -/
def NoHarm (m : AliasMap) (base after : Certificate) (js : List Judgment) : Prop :=
  ∀ b ∈ base.decls, DeclOk m after js b

/-- The last part of the invariant: every commit on the mend branch is an
accepted patch. The mend branch is modelled as the list of its patches; the
type `Accepted` carries the evidence, so this holds by construction. -/
def BranchSound (branch : List Accepted) : Prop :=
  ∀ p ∈ branch,
    (p.declIndexBefore < p.declIndexAfter ∨
      (p.declIndexBefore = p.declIndexAfter ∧ p.reachAfter < p.reachBefore)) ∧
    p.candidate.clean = true ∧ p.lintAtEdit = 0

theorem branchSound (branch : List Accepted) : BranchSound branch :=
  fun p _ => ⟨p.progress, p.clean, p.lintFree⟩

end LeanMend
