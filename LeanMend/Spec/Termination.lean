import LeanMend.Core.Run

/-!
# Termination

The run stops (`docs/machine.md` § Termination, concept D5). There is no
retry cap; these theorems are the reason the loops end.

* Level 2: every successful `Mending.step` makes `Mending.measure` fall in the
  lexicographic order on `Nat × Nat × Nat × Nat × Nat` (`docs/parallel.md`
  X5, widened by the open-site count). An accepted edit moves the earliest
  open position strictly later (X3); giving up on the head always removes
  one open site, even when the newly-exposed head ties the old head's
  position.
* Level 1: leaving `Mending` closes one open module, and a settled rebuild
  never opens a module. So `openCount` falls once per frontier module. A
  `moduleBuild` that unblocks a module keeps `openCount` or lowers it, and
  lowers `blockedCount` (`docs/parallel.md` P21).
* Level 3: a separate phase, after Level 1 and Level 2 both reach a fixpoint
  (`docs/machine.md` § Termination, Level 3). Every successful
  `FindingMending.step` makes `FindingMending.measure` fall in the
  lexicographic order on `Nat × Nat`: the open findings at a site still in
  `sites`, then the candidates left, summed over those sites. `accept` and
  `giveUp` both remove the head site from `sites`, lowering the first item by
  the site's own finding count (never zero, `groupFindingSites` never builds
  an empty group); `reject` leaves `sites` the same length and drops one
  candidate, lowering the second item.
-/

namespace LeanMend

/-- The lexicographic order on the level-2 measure. -/
abbrev MeasureLt : Nat × Nat × Nat × Nat × Nat → Nat × Nat × Nat × Nat × Nat → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))))

/-- A strict decrease at the first component, or a tie there and a strict
decrease at the second, closes a `MeasureLt` goal regardless of the
remaining three components. -/
theorem measureLt_of_lt_or_eq_lt {a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : Nat}
    (h : a1 < b1 ∨ (a1 = b1 ∧ a2 < b2)) :
    MeasureLt (a1, a2, a3, a4, a5) (b1, b2, b3, b4, b5) := by
  rcases h with h | ⟨rfl, h⟩
  · apply Prod.Lex.left; exact h
  · apply Prod.Lex.right; apply Prod.Lex.left; exact h

/-- A non-strict decrease at the first component (with a conditional
non-strict decrease at the second, should the first tie) and an
unconditional strict decrease at the third closes a `MeasureLt` goal: the
third component is the fallback the first two cannot always deliver on
their own (`Mending.gaveUp_measure`). -/
theorem measureLt_of_le_le_lt {a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : Nat}
    (h1 : a1 ≤ b1) (h2 : a1 = b1 → a2 ≤ b2) (h3 : a3 < b3) :
    MeasureLt (a1, a2, a3, a4, a5) (b1, b2, b3, b4, b5) := by
  by_cases heq1 : a1 = b1
  · subst heq1
    apply Prod.Lex.right
    by_cases heq2 : a2 = b2
    · subst heq2
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact h3
    · apply Prod.Lex.left
      have := h2 rfl
      omega
  · apply Prod.Lex.left
    omega

theorem Mending.reject_measure (m : Mending) {o₀ : Open} {rest : List Open}
    (hs : m.sites = o₀ :: rest) (hc : o₀.candidates ≠ []) :
    MeasureLt (m.reject hs).measure m.measure := by
  simp only [Mending.measure, Mending.reject, hs, List.length_cons]
  apply Prod.Lex.right
  apply Prod.Lex.right
  apply Prod.Lex.right
  apply Prod.Lex.left
  rw [List.length_drop]
  have : 0 < o₀.candidates.length := List.length_pos_iff.mpr hc
  omega

/-- A cleaning (Lean's hint) keeps the error count and the candidate count, and
shortens the head candidate's replacement. -/
theorem Mending.refine_measure (m : Mending) {o₀ : Open} {rest : List Open}
    {c : Candidate} {cs : List Candidate} (hs : m.sites = o₀ :: rest)
    (hc : o₀.candidates = c :: cs) (c' : Candidate)
    (hlt : c'.replacement.length < c.replacement.length) :
    MeasureLt (m.refine hs c').measure m.measure := by
  have hlen : (c' :: List.drop 1 o₀.candidates).length = o₀.candidates.length := by
    simp [hc]
  simp only [Mending.measure, Mending.refine, hs, List.length_cons, hlen]
  apply Prod.Lex.right
  apply Prod.Lex.right
  apply Prod.Lex.right
  apply Prod.Lex.right
  simp [hc, hlt]

/-- Removing the head site to residue always lowers the open-site count, even
when the newly-exposed head's position and candidate count do not improve on
the old head's: giving up on a module's only open site, or on a site whose
successor happens to share its position, still makes progress. -/
theorem Mending.gaveUp_measure (m : Mending) {o₀ : Open} {rest : List Open}
    (hs : m.sites = o₀ :: rest) :
    MeasureLt (m.giveUp hs).measure m.measure := by
  have hb0 : o₀.site.declIndex < m.decls := m.bounded o₀ (hs ▸ List.mem_cons_self ..)
  have hsorted : List.Pairwise (fun a b => Open.le a b = true) (o₀ :: rest) := hs ▸ m.sorted
  simp only [Mending.measure, Mending.giveUp, hs]
  rcases rest with _ | ⟨o₁, rest'⟩
  · apply measureLt_of_le_le_lt (a3 := 0) (b3 := (o₀ :: ([] : List Open)).length)
    · omega
    · intro _; omega
    · simp
  · have hb1 : o₁.site.declIndex < m.decls :=
      m.bounded o₁ (hs ▸ List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have hle := (List.pairwise_cons.mp hsorted).1 o₁ (List.mem_cons_self ..)
    simp only [Open.le_iff, Site.earlier, Site.key, keyLt_iff] at hle
    apply measureLt_of_le_le_lt
      (a3 := (o₁ :: rest').length) (b3 := (o₀ :: o₁ :: rest').length)
    · omega
    · intro heq; omega
    · simp

/-- An accepted candidate moves the earliest open position strictly later
(`docs/parallel.md` X3): a later declaration, or the same declaration with a
smaller `Site.reach`. When every error is resolved, the open-site count
drops to zero and that alone is enough, whatever the old head's position. -/
theorem Mending.accept_measure (m : Mending) {o₀ : Open} {rest : List Open}
    (hs : m.sites = o₀ :: rest) (c : Candidate) (e lint : Nat) (sites : List Open)
    (hBound : ∀ o ∈ sites, o.site.declIndex < m.decls)
    (hp : o₀.site.declIndex < (Mending.afterCoord o₀ sites).1 ∨
      (o₀.site.declIndex = (Mending.afterCoord o₀ sites).1 ∧
        (Mending.afterCoord o₀ sites).2 < o₀.site.reach))
    (hclean : c.clean = true ∧ lint = 0)
    (hwf : (Mending.sortOpens sites).length + m.residue.length ≤ e) :
    MeasureLt (m.accept hs c e lint sites hBound hp hclean hwf).measure m.measure := by
  have hb0 : o₀.site.declIndex < m.decls := m.bounded o₀ (hs ▸ List.mem_cons_self ..)
  simp only [Mending.measure, Mending.accept, hs]
  rcases hsort : Mending.sortOpens sites with _ | ⟨o', t'⟩
  · apply measureLt_of_le_le_lt (a1 := 0) (a2 := 0) (a3 := 0)
      (b3 := (o₀ :: rest).length)
    · omega
    · intro _; omega
    · simp
  · simp only [hsort, Mending.afterCoord, List.head?_cons, Option.map_some,
      Option.getD_some] at hp
    have ho' : o' ∈ sites := by
      have hmem : o' ∈ Mending.sortOpens sites := by rw [hsort]; exact List.mem_cons_self ..
      exact List.mem_mergeSort.mp hmem
    have hb1 : o'.site.declIndex < m.decls := hBound o' ho'
    apply measureLt_of_lt_or_eq_lt
    rcases hp with hlt | ⟨heq, hlt⟩
    · left; omega
    · right; exact ⟨by omega, hlt⟩

/-- Level 2 ends: every successful step lowers the measure. -/
theorem Mending.step_measure (m m' : Mending) (o : MendObs)
    (h : m.step o = .ok m') : MeasureLt m'.measure m.measure := by
  unfold Mending.step at h
  split at h
  · -- gaveUp: the head site becomes residue
    rename_i o₀ rest hs
    split at h
    · cases h
      exact Mending.gaveUp_measure m hs
    · cases h
  · -- unparsable: reject
    rename_i o₀ rest hs
    split at h
    · cases h
    · cases h
      rename_i hne
      exact Mending.reject_measure m hs (by simpa using hne)
  · -- rebuilt
    rename_i o₀ rest e lint unused sites hs
    split at h
    · cases h
    · rename_i c cs hc
      have hne : o₀.candidates ≠ [] := by simp [hc]
      split at h  -- hBound
      · split at h  -- the exposure guard
        · split at h  -- hp
          · split at h  -- hclean
            · split at h  -- hwf: accept
              · cases h
                rename_i hBound _hg hp hclean hwf
                exact Mending.accept_measure m hs c e lint sites hBound hp hclean hwf
              · cases h
            · -- hclean false: Lean's hint, or reject
              split at h  -- the unused-simp-args check
              · split at h  -- dropSimpArgs
                · split at h  -- the replacement-length check
                  · cases h
                    rename_i r _ hlt
                    exact Mending.refine_measure m hs hc _ hlt
                  · cases h; exact Mending.reject_measure m hs hne
                · cases h; exact Mending.reject_measure m hs hne
              · cases h; exact Mending.reject_measure m hs hne
          · cases h; exact Mending.reject_measure m hs hne
        · cases h; exact Mending.reject_measure m hs hne
      · cases h
  · cases h

private theorem countP_le_of_imp {α} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) : l.countP p ≤ l.countP q := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.countP_cons]
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    have ha := h a (List.mem_cons_self ..)
    split <;> split <;> simp_all <;> omega

private theorem countP_lt_of_imp {α} (l : List α) (p q : α → Bool)
    (h : ∀ x ∈ l, p x = true → q x = true) (a : α) (ha : a ∈ l)
    (hp : p a = false) (hq : q a = true) : l.countP p < l.countP q := by
  induction l with
  | nil => cases ha
  | cons b l ih =>
    simp only [List.countP_cons]
    have hle := countP_le_of_imp l p q (fun x hx => h x (List.mem_cons_of_mem b hx))
    have hb := h b (List.mem_cons_self ..)
    rcases List.mem_cons.mp ha with rfl | hal
    · simp_all; omega
    · have := ih (fun x hx => h x (List.mem_cons_of_mem b hx)) hal
      split <;> split <;> simp_all <;> omega

/-- Level 1: a settled rebuild never opens a module. -/
theorem openCount_settled (mods : List Module) (st st' : Statuses)
    (h : Settled mods st st') : openCount mods st' ≤ openCount mods st := by
  apply countP_le_of_imp
  intro m hm hopen
  cases hst : (st m.name).isOpen
  · have := h m hm hst
    simp_all
  · rfl

/-- Level 1: leaving `Mending` closes the module, so `openCount` falls. -/
theorem openCount_finish (mods : List Module) (st : Statuses) (m : Module)
    (hm : m ∈ mods) (hopen : (st m.name).isOpen = true) (s : ModStatus)
    (hs : s.isOpen = false) : openCount mods (finish st m.name s) < openCount mods st := by
  refine countP_lt_of_imp _ _ _ ?_ m hm (by simp [finish, hs]) hopen
  intro x _ hx
  unfold finish at hx
  split at hx
  · simp_all
  · exact hx

/-- Finish every module of a list at once, each with the status `s` gives
it (`docs/parallel.md` § Level 2). -/
def finishAll (s : String → ModStatus) : List String → Statuses → Statuses
  | [], st => st
  | n :: rest, st => finishAll s rest (finish st n (s n))

/-- `finish` to a non-open status never raises `openCount`, whatever the
module's status was before. -/
theorem openCount_finish_le (mods : List Module) (st : Statuses) (name : String) (s : ModStatus)
    (hs : s.isOpen = false) : openCount mods (finish st name s) ≤ openCount mods st := by
  apply countP_le_of_imp
  intro m _ hopen
  by_cases heq : m.name = name
  · simp [finish, heq, hs] at hopen
  · simpa [finish, heq] using hopen

/-- `finishAll` to non-open statuses never raises `openCount`: each step is
`openCount_finish_le`, chained. -/
theorem openCount_finishAll_le (mods : List Module) (s : String → ModStatus) :
    ∀ (ns : List String), (∀ n ∈ ns, (s n).isOpen = false) → ∀ (st : Statuses),
      openCount mods (finishAll s ns st) ≤ openCount mods st
  | [], _, st => by simp [finishAll]
  | n :: rest, hs, st =>
    Nat.le_trans
      (by
        show openCount mods (finishAll s rest (finish st n (s n))) ≤ openCount mods (finish st n (s n))
        exact openCount_finishAll_le mods s rest
          (fun x hx => hs x (List.mem_cons_of_mem n hx)) (finish st n (s n)))
      (openCount_finish_le mods st n (s n) (hs n (List.mem_cons_self ..)))

/-- Level 1: finishing a non-empty list of open modules (`docs/parallel.md`
§ Level 2, generalizing `openCount_finish`) makes `openCount` fall: one of
the modules is open in `st` and closes, and no other module of the list can
raise the count back. -/
theorem openCount_finishAll (mods : List Module) (st : Statuses) (ns : List String)
    (hne : ns ≠ [])
    (hns : ∀ n ∈ ns, ∃ m ∈ mods, m.name = n ∧ (st m.name).isOpen = true)
    (s : String → ModStatus) (hs : ∀ n ∈ ns, (s n).isOpen = false) :
    openCount mods (finishAll s ns st) < openCount mods st := by
  cases ns with
  | nil => exact absurd rfl hne
  | cons n rest =>
    obtain ⟨m, hmem, hname, hmopen⟩ := hns n (List.mem_cons_self ..)
    have hstep : openCount mods (finish st n (s n)) < openCount mods st := by
      have h := openCount_finish mods st m hmem hmopen (s n) (hs n (List.mem_cons_self ..))
      rwa [hname] at h
    have hrest : openCount mods (finishAll s rest (finish st n (s n))) ≤
        openCount mods (finish st n (s n)) :=
      openCount_finishAll_le mods s rest (fun x hx => hs x (List.mem_cons_of_mem n hx))
        (finish st n (s n))
    calc openCount mods (finishAll s (n :: rest) st)
        = openCount mods (finishAll s rest (finish st n (s n))) := by rw [finishAll]
      _ ≤ openCount mods (finish st n (s n)) := hrest
      _ < openCount mods st := hstep

/-- A frontier module is open, so `openCount_finish` applies to it. -/
theorem frontier_open (mods : List Module) (st : Statuses) (n : String)
    (h : n ∈ frontier mods st) : ∃ m ∈ mods, m.name = n ∧ (st m.name).isOpen = true := by
  simp only [frontier, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨m, ⟨hm, hfail, _⟩, rfl⟩ := h
  exact ⟨m, hm, rfl, by simp [hfail, ModStatus.isOpen]⟩

/-- The modules that are `blocked`: the second component of the level-1
measure, after `openCount` (`docs/parallel.md` P21). -/
def blockedCount (mods : List Module) (st : Statuses) : Nat :=
  mods.countP fun m => st m.name == .blocked

/-- Level 1: a `moduleBuild` that unblocks a module lowers `blockedCount`,
and as a settled step (`RunState.moduleBuilt_settled`) it never raises
`openCount`. So the pair (`openCount`, `blockedCount`) falls
lexicographically at each unblocking build (`docs/parallel.md` P21). -/
theorem blockedCount_moduleBuilt (c : Context) (st st' : Statuses) (name : String)
    (s : ModStatus) (hb : st name = .blocked)
    (h : RunState.moduleBuilt c st name s = .built c st') :
    blockedCount c.mods st' < blockedCount c.mods st := by
  unfold RunState.moduleBuilt at h
  rw [hb] at h
  simp only at h
  split at h
  · rename_i hguard
    cases h
    obtain ⟨hready, hs⟩ := hguard
    obtain ⟨m, hm, hname, _, _⟩ := ready_imports_built c.mods st name hready
    subst hname
    refine countP_lt_of_imp _ _ _ ?_ m hm ?_ (by simp [hb])
    · intro x _ hx
      unfold finish at hx
      split at hx
      · rcases hs with hs | hs <;> simp_all
      · exact hx
    · rcases hs with hs | hs <;> simp [finish, hs]
  · cases h

/-! ## Level 3: inside `FindingMending` -/

/-- The lexicographic order on the level-3 measure. -/
abbrev FindingMeasureLt : Nat × Nat → Nat × Nat → Prop := Prod.Lex (· < ·) (· < ·)

/-- A `reject` leaves every site's group untouched and drops one candidate
from the head's own list, so the measure's second item strictly falls with
the first unchanged. -/
theorem FindingMending.reject_measure (m : FindingMending) {o₀ : OpenFindingSite}
    {rest : List OpenFindingSite} (hs : m.sites = o₀ :: rest) (hc : o₀.candidates ≠ []) :
    FindingMeasureLt (m.reject hs).measure m.measure := by
  simp only [FindingMending.measure, FindingMending.openFindingCount,
    FindingMending.candidatesLeft, FindingMending.reject, hs, List.map_cons, List.sum_cons,
    List.length_drop]
  apply Prod.Lex.right
  have : 0 < o₀.candidates.length := List.length_pos_iff.mpr hc
  omega

/-- Giving up always lowers `openFindingCount`: the head site leaves
`sites`, and it closes at least one finding (`groupFindingSites` never
builds an empty group), whatever the measure's second item does. -/
theorem FindingMending.gaveUp_measure (m : FindingMending) {o₀ : OpenFindingSite}
    {rest : List OpenFindingSite} (hs : m.sites = o₀ :: rest) :
    FindingMeasureLt (m.giveUp hs).measure m.measure := by
  have hmem : o₀.group.members ≠ [] := m.nonempty o₀ (hs ▸ List.mem_cons_self ..)
  have hlen : 0 < o₀.group.members.length := List.length_pos_iff.mpr hmem
  simp only [FindingMending.measure, FindingMending.openFindingCount, FindingMending.giveUp, hs,
    List.map_cons, List.sum_cons]
  apply Prod.Lex.left
  omega

/-- Accepting always lowers `openFindingCount`, the same way giving up does:
the head site leaves `sites`, closing at least one finding. -/
theorem FindingMending.accept_measure (m : FindingMending) {o₀ : OpenFindingSite}
    {rest : List OpenFindingSite} (hs : m.sites = o₀ :: rest) (c : Candidate)
    (baselineRestored noNewFinding stillBuilds : Bool)
    (hAccept : baselineRestored = true ∧ noNewFinding = true ∧ stillBuilds = true) :
    FindingMeasureLt
      (m.accept hs c baselineRestored noNewFinding stillBuilds hAccept).measure m.measure := by
  have hmem : o₀.group.members ≠ [] := m.nonempty o₀ (hs ▸ List.mem_cons_self ..)
  have hlen : 0 < o₀.group.members.length := List.length_pos_iff.mpr hmem
  simp only [FindingMending.measure, FindingMending.openFindingCount, FindingMending.accept, hs,
    List.map_cons, List.sum_cons]
  apply Prod.Lex.left
  omega

/-- Level 3 ends: every successful step lowers the measure. -/
theorem FindingMending.step_measure (m m' : FindingMending) (o : FindingObs)
    (h : m.step o = .ok m') : FindingMeasureLt m'.measure m.measure := by
  unfold FindingMending.step at h
  split at h
  · -- gaveUp: the head site leaves `sites` for `exhausted`
    rename_i o₀ rest hs
    split at h
    · cases h
      exact FindingMending.gaveUp_measure m hs
    · cases h
  · -- rejected: drop the head candidate
    rename_i o₀ rest hs
    split at h
    · cases h
    · cases h
      rename_i hne
      exact FindingMending.reject_measure m hs (by simpa using hne)
  · -- accepted: all three conditions must hold
    rename_i o₀ rest baselineRestored noNewFinding stillBuilds hs
    split at h
    · cases h
    · rename_i c cs _hc
      split at h
      · cases h
        rename_i hAccept
        exact FindingMending.accept_measure m hs c baselineRestored noNewFinding stillBuilds hAccept
      · cases h
  · cases h

/-- An accepted repair removes at least one finding: the closed-findings
list is non-empty by construction (`FindingMending.nonempty`). -/
theorem FindingAccepted.closes_at_least_one (a : FindingAccepted) : a.closed ≠ [] :=
  a.closedNonempty

/-- An accepted repair adds no finding: condition 2 of § Acceptance is part
of the observation itself, carried on `FindingAccepted` the same way
`Accepted.lintFree` carries its own evidence (`BranchSound`,
`LeanMend/Spec/Invariant.lean`). -/
theorem FindingAccepted.adds_no_finding (a : FindingAccepted) : a.noNewFinding = true :=
  a.conditionsHeld.2.1

end LeanMend
