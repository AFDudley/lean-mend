import LeanMend.Core.Run

/-!
# Termination

The run stops (`docs/machine.md` § Termination, concept D5). There is no
retry cap; these theorems are the reason the loops end.

* Level 2: every successful `Mending.step` makes `Mending.measure` fall in the
  lexicographic order on `Nat × Nat`.
* Level 1: leaving `Mending` closes one open module, and a settled rebuild
  never opens a module. So `openCount` falls once per frontier module.
-/

namespace LeanMend

/-- The lexicographic order on the level-2 measure. -/
abbrev MeasureLt : Nat × Nat → Nat × Nat → Prop := Prod.Lex (· < ·) (· < ·)

theorem Mending.reject_measure (m : Mending) (o₀ : Open) (rest : List Open)
    (hs : m.sites = o₀ :: rest) (hc : o₀.candidates ≠ []) :
    MeasureLt m.reject.measure m.measure := by
  unfold Mending.reject Mending.measure
  split
  · simp_all
  · rename_i o rest' h
    rw [hs] at h
    injection h with h1 h2
    subst h1
    apply Prod.Lex.right
    simp only [h, List.head?_cons, Option.map_some, Option.getD_some, List.length_drop]
    have : 0 < o₀.candidates.length := List.length_pos_iff.mpr hc
    omega

/-- Level 2 ends: every successful step lowers the measure. -/
theorem Mending.step_measure (m m' : Mending) (o : MendObs)
    (h : m.step o = .ok m') : MeasureLt m'.measure m.measure := by
  unfold Mending.step at h
  split at h
  · -- gaveUp: the head site becomes residue
    rename_i o₀ rest hs
    split at h
    · cases h
      apply Prod.Lex.left
      have := m.wf
      simp only [hs, List.length_cons] at this
      show m.errors - 1 < m.errors
      omega
    · cases h
  · -- unparsable: reject
    rename_i o₀ rest hs
    split at h
    · cases h
    · cases h
      rename_i hne
      exact Mending.reject_measure m o₀ rest hs (by simpa using hne)
  · -- rebuilt
    rename_i o₀ rest e lint sites hs
    split at h
    · cases h
    · rename_i c cs hc
      have hne : o₀.candidates ≠ [] := by simp [hc]
      split at h
      · split at h
        · split at h
          · cases h
            rename_i hfell _ _
            apply Prod.Lex.left
            show e - m.residue.length < m.errors
            omega
          · cases h
        · cases h; exact Mending.reject_measure m o₀ rest hs hne
      · cases h; exact Mending.reject_measure m o₀ rest hs hne
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

/-- A frontier module is open, so `openCount_finish` applies to it. -/
theorem frontier_open (mods : List Module) (st : Statuses) (n : String)
    (h : n ∈ frontier mods st) : ∃ m ∈ mods, m.name = n ∧ (st m.name).isOpen = true := by
  simp only [frontier, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨m, ⟨hm, hfail, _⟩, rfl⟩ := h
  exact ⟨m, hm, rfl, by simp [hfail, ModStatus.isOpen]⟩

end LeanMend
