import LeanMend.Core.Cause
import LeanMend.Spec.Types

/-!
# Level 2 and Level 3: inside `Mending` and `FindingMending`

One frontier module, its open sites and the candidates of the head site
(`Mending`, `docs/machine.md` § Level 2); one repair-frontier module, its
open finding-sites and their candidates (`FindingMending`, § Level 3,
`FindingMending`). Every function here is pure. The shell makes the
observation, records it in the ledger, and then calls `Mending.step` or
`FindingMending.step`.
-/

namespace LeanMend

/-- An open site and the candidates still to try, in rule order. The state
holds what is left, not what was tried (concept B6). -/
structure Open where
  site : Site
  candidates : List Candidate
  deriving Repr

/-- The same failure after an edit elsewhere in the file: byte positions
move, so a site is identified by its declaration, class and message. -/
def Site.sameAs (a b : Site) : Bool :=
  a.decl == b.decl && a.diagnostic.kind == b.diagnostic.kind && a.diagnostic.text == b.diagnostic.text

/-- `a` may sit before `b` in the sorted order: `b`'s position is not
strictly before `a`'s (`docs/parallel.md` X2). -/
def Open.le (a b : Open) : Bool := !(b.site.earlier a.site)

theorem Open.le_iff (a b : Open) : Open.le a b = true ↔ ¬ b.site.earlier a.site = true := by
  unfold Open.le
  cases b.site.earlier a.site <;> simp

theorem Open.le_trans (a b c : Open) (hab : Open.le a b = true) (hbc : Open.le b c = true) :
    Open.le a c = true := by
  rw [Open.le_iff] at hab hbc ⊢
  intro hca
  rcases Site.earlier_total b.site a.site with h1 | h2 | h3
  · exact absurd h1 hab
  · exact hbc (Site.earlier_trans hca h2)
  · rw [Site.earlier_congr_right h3.symm] at hca; exact hbc hca

theorem Open.le_total (a b : Open) : Open.le a b || Open.le b a := by
  rw [Bool.or_eq_true, Open.le_iff, Open.le_iff]
  rcases Site.earlier_total b.site a.site with h | h | h
  · exact Or.inr (Site.earlier_asymm h)
  · exact Or.inl (Site.earlier_asymm h)
  · refine Or.inl fun h2 => ?_
    unfold Site.earlier at h2
    rw [h] at h2
    exact keyLt_irrefl _ h2

/-- The state of one module in `Mending`. -/
structure Mending where
  module : String
  /-- Error sites in the module that are not marked residue. -/
  errors : Nat
  /-- The module's declaration count, fixed by decision D10
  (`docs/parallel.md` X6). -/
  decls : Nat
  sites : List Open
  residue : List Site
  accepted : List Accepted
  /-- Each open site is one unresolved error. -/
  wf : sites.length ≤ errors
  /-- Every open site's declaration index is one of the module's declarations. -/
  bounded : ∀ o ∈ sites, o.site.declIndex < decls
  /-- The open sites are kept in source-position order: the head is never
  strictly after another open site (`docs/parallel.md` X2). -/
  sorted : List.Pairwise (fun a b => Open.le a b = true) sites

/-- What the shell must do next. -/
inductive MendAction where
  /-- Apply this candidate in an attempt worktree and rebuild the module. -/
  | attempt (c : Candidate)
  /-- The head site has no candidate left. -/
  | giveUp (s : Site)
  /-- No open site is left. -/
  | finish

/-- What the shell saw. -/
inductive MendObs where
  /-- The probe could not parse the candidate at its node kind. -/
  | unparsable
  /-- The module rebuilt with the candidate applied. `errors` is the module's
  whole error count, residue sites included. `lint` counts the linter
  warnings (kind `linter.*`) inside the replaced bytes: warnings the candidate
  itself caused. `unused` lists the simp arguments that Lean reports as
  unused among those warnings (`linter.unusedSimpArgs`, "This simp argument
  is unused: x"). `sites` are the open sites the shell read from the new
  diagnostics, with their candidates, without the residue sites
  (`Site.sameAs`). -/
  | rebuilt (errors : Nat) (lint : Nat) (unused : List String) (sites : List Open)
  /-- The shell recorded the head site as residue. -/
  | gaveUp

def Mending.next (m : Mending) : MendAction :=
  match m.sites with
  | [] => .finish
  | o :: _ =>
    match o.candidates with
    | [] => .giveUp o.site
    | c :: _ => .attempt c

/-- The next `n` head candidates of the head site, in rule order
(`docs/parallel.md` P14). The shell attempts every one of them at the same
time, each in its own worktree. Acceptance stays `Mending.step`: the shell
feeds the verdicts back to it in this same order, a reject for every
candidate that failed before the first one it accepts (P15). -/
def Mending.speculate (m : Mending) (n : Nat) : List Candidate :=
  match m.sites with
  | [] => []
  | o :: _ => o.candidates.take n

/-- `Mending.speculate m n` is a prefix of the head site's candidate list, so
the speculative order is the rule order (`docs/parallel.md`
`speculate_prefix`). -/
theorem Mending.speculate_prefix (m : Mending) {o₀ : Open} {rest : List Open}
    (hs : m.sites = o₀ :: rest) (n : Nat) :
    Mending.speculate m n <+: o₀.candidates := by
  unfold Mending.speculate
  rw [hs]
  exact List.take_prefix n o₀.candidates

/-- Changing a site's candidates keeps every site's declaration index the
same, so a declaration bound on the old list transfers to the new one. -/
theorem Mending.bounded_setHead {decls : Nat} {o : Open} {rest : List Open} (cs : List Candidate)
    (h : ∀ x ∈ o :: rest, x.site.declIndex < decls) :
    ∀ x ∈ { o with candidates := cs } :: rest, x.site.declIndex < decls := by
  intro x hx
  rcases List.mem_cons.mp hx with hx | hx
  · subst hx; exact h o (List.mem_cons_self ..)
  · exact h x (List.mem_cons_of_mem _ hx)

/-- Changing a site's candidates keeps every site's position the same, so a
sortedness fact on the old list transfers to the new one. -/
theorem Mending.sorted_setHead {o : Open} {rest : List Open} (cs : List Candidate)
    (h : List.Pairwise (fun a b => Open.le a b = true) (o :: rest)) :
    List.Pairwise (fun a b => Open.le a b = true) ({ o with candidates := cs } :: rest) := by
  rw [List.pairwise_cons] at h ⊢
  exact h

/-- Give up on the head site: it becomes residue. Takes the split of
`m.sites` explicitly; see `Mending.reject`. -/
def Mending.giveUp (m : Mending) {o₀ : Open} {rest : List Open} (hs : m.sites = o₀ :: rest) :
    Mending :=
  { m with
    errors := m.errors - 1
    sites := rest
    residue := o₀.site :: m.residue
    wf := by have := m.wf; rw [hs] at this; simp_all; omega
    bounded := fun x hx => m.bounded x (hs ▸ List.mem_cons_of_mem _ hx)
    sorted := (List.pairwise_cons.mp (hs ▸ m.sorted)).2 }

/-- Drop the head candidate of the head site. Takes the split of `m.sites`
explicitly (rather than re-matching it internally) so a caller that already
has `o₀`, `rest` and `hs` on hand (`Mending.step`) gets back a result whose
`sites` field is `rfl`-transparent in them, which `Mending.reject_measure`
relies on. -/
def Mending.reject (m : Mending) {o₀ : Open} {rest : List Open} (hs : m.sites = o₀ :: rest) :
    Mending :=
  { m with
    sites := { o₀ with candidates := o₀.candidates.drop 1 } :: rest
    wf := by have := m.wf; rw [hs] at this; simpa using this
    bounded := Mending.bounded_setHead _ (hs ▸ m.bounded)
    sorted := Mending.sorted_setHead _ (hs ▸ m.sorted) }

/-- One simp list's items, split at the commas outside brackets. -/
private def splitItems (cs : List Char) : List (List Char) :=
  let (items, cur, _) := cs.foldl (init := (([] : List (List Char)), ([] : List Char), (0 : Nat)))
    fun (items, cur, depth) c =>
      if c == ',' && depth == 0 then (items ++ [cur], [], depth)
      else if c == '[' || c == '(' || c == '{' then (items, cur ++ [c], depth + 1)
      else if c == ']' || c == ')' || c == '}' then (items, cur ++ [c], depth - 1)
      else (items, cur ++ [c], depth)
  items ++ [cur]

/-- Lean's hint for `linter.unusedSimpArgs`, applied: every named argument is
removed from the first `[...]` list of a replacement, and the list itself if it
becomes empty. `none` if a named argument is not an item of that list. -/
def dropSimpArgs (repl : String) (args : List String) : Option String := do
  let cs := repl.toList
  let open_ ← cs.findIdx? (· == '[')
  -- the matching `]`
  let (close?, _) := (cs.drop (open_ + 1)).zipIdx.foldl (init := ((none : Option Nat), (1 : Nat)))
    fun (found, d) (c, i) => match found with
      | some _ => (found, d)
      | none =>
        if c == '[' then (none, d + 1)
        else if c == ']' then (if d == 1 then (some (open_ + 1 + i), 0) else (none, d - 1))
        else (none, d)
  let close ← close?
  let items := splitItems ((cs.drop (open_ + 1)).take (close - open_ - 1))
  let name (it : List Char) : String :=
    let t := (String.ofList it).trimAscii.toString
    if t.startsWith "← " then (String.ofList (t.toList.drop 2)).trimAscii.toString else t
  guard (args.all fun a => items.any fun it => name it == a)
  -- Keep the layout: a kept item after removed ones takes the leading
  -- whitespace of the first removed item, so only the argument disappears.
  let ws (it : List Char) := it.takeWhile Char.isWhitespace
  let (kept, _) := items.foldl (init := (([] : List (List Char)), (none : Option (List Char))))
    fun (acc, pending) it =>
      if args.contains (name it) then (acc, pending.orElse fun _ => some (ws it))
      else match pending with
        | some w => (acc ++ [w ++ it.dropWhile Char.isWhitespace], none)
        | none => (acc ++ [it], none)
  let before := cs.take open_
  let after := cs.drop (close + 1)
  match kept with
  | [] =>
    -- no argument left: drop the list and the space before it
    let before := if before.getLast? == some ' ' then before.dropLast else before
    pure (String.ofList (before ++ after))
  | k :: ks =>
    -- the first kept item starts the list: no leading whitespace
    let k := if items.head? == some k then k else k.dropWhile Char.isWhitespace
    let inner := ([k] ++ ks).foldl (init := ([] : List Char)) fun acc it =>
      if acc.isEmpty then it else acc ++ [','] ++ it
    pure (String.ofList (before ++ ['['] ++ inner ++ [']'] ++ after))

/-- Replace the head candidate of the head site with its cleaned form.
Takes the split of `m.sites` explicitly; see `Mending.reject`. -/
def Mending.refine (m : Mending) {o₀ : Open} {rest : List Open} (hs : m.sites = o₀ :: rest)
    (c' : Candidate) : Mending :=
  { m with
    sites := { o₀ with candidates := c' :: o₀.candidates.drop 1 } :: rest
    wf := by have := m.wf; rw [hs] at this; simpa using this
    bounded := Mending.bounded_setHead _ (hs ▸ m.bounded)
    sorted := Mending.sorted_setHead _ (hs ▸ m.sorted) }

/-- The open sites in source-position order (`docs/parallel.md` X2): the head
is the earliest error, not the first in the shell's (Lean message) order. -/
def Mending.sortOpens (os : List Open) : List Open := os.mergeSort Open.le

/-- The head of `Mending.sortOpens` is earlier than, or ties, every open site:
no site of `os` is strictly before it (`Mending.sort_head_earliest`,
`docs/parallel.md`). -/
theorem Mending.sortOpens_head_min (os : List Open) (h : Open) (t : List Open)
    (heq : Mending.sortOpens os = h :: t) (o : Open) (ho : o ∈ os) :
    ¬ o.site.earlier h.site = true := by
  have hp := List.pairwise_mergeSort Open.le_trans Open.le_total os
  have hmem : o ∈ Mending.sortOpens os := List.mem_mergeSort.mpr ho
  have heq' : os.mergeSort Open.le = h :: t := heq
  rw [heq'] at hp
  rw [heq] at hmem
  rcases List.mem_cons.mp hmem with rfl | hmem'
  · exact Site.earlier_irrefl _
  · rw [← Open.le_iff]; exact (List.pairwise_cons.mp hp).1 o hmem'

theorem Mending.sortOpens_length (os : List Open) : (Mending.sortOpens os).length = os.length :=
  List.length_mergeSort os

theorem Mending.sortOpens_bounded {decls : Nat} {os : List Open}
    (h : ∀ o ∈ os, o.site.declIndex < decls) :
    ∀ o ∈ Mending.sortOpens os, o.site.declIndex < decls :=
  fun o ho => h o (List.mem_mergeSort.mp ho)

theorem Mending.sortOpens_sorted (os : List Open) :
    List.Pairwise (fun a b => Open.le a b = true) (Mending.sortOpens os) := by
  unfold Mending.sortOpens
  exact List.pairwise_mergeSort Open.le_trans Open.le_total os

/-- The head candidate's position-coordinate progress after a `rebuilt`
observation: the declaration index and `Site.reach` of the new sorted head,
or a strictly-later sentinel when every error in `sites` is resolved. -/
def Mending.afterCoord (o₀ : Open) (sites : List Open) : Nat × Nat :=
  let sorted := Mending.sortOpens sites
  ((sorted.head?.map (·.site.declIndex)).getD (o₀.site.declIndex + 1),
   (sorted.head?.map (·.site.reach)).getD 0)

/-- Accept a `rebuilt` candidate: commit it, and move the head to the sorted
open sites the shell reported (`docs/parallel.md` X1-X4). Factored out of
`Mending.step` so `Mending.accept_measure` can be proved on its own. -/
def Mending.accept (m : Mending) {o₀ : Open} {rest : List Open} (_hs : m.sites = o₀ :: rest)
    (c : Candidate) (e lint : Nat) (sites : List Open)
    (hBound : ∀ o ∈ sites, o.site.declIndex < m.decls)
    (hp : o₀.site.declIndex < (Mending.afterCoord o₀ sites).1 ∨
      (o₀.site.declIndex = (Mending.afterCoord o₀ sites).1 ∧
        (Mending.afterCoord o₀ sites).2 < o₀.site.reach))
    (hclean : c.clean = true ∧ lint = 0)
    (hwf : (Mending.sortOpens sites).length + m.residue.length ≤ e) : Mending :=
  { m with
    errors := e - m.residue.length
    sites := Mending.sortOpens sites
    accepted :=
      { candidate := c, errorsBefore := m.errors + m.residue.length, errorsAfter := e,
        declIndexBefore := o₀.site.declIndex, declIndexAfter := (Mending.afterCoord o₀ sites).1,
        reachBefore := o₀.site.reach, reachAfter := (Mending.afterCoord o₀ sites).2,
        progress := hp, clean := hclean.1, lintAtEdit := lint, lintFree := hclean.2 } :: m.accepted
    wf := by omega
    bounded := Mending.sortOpens_bounded hBound
    sorted := Mending.sortOpens_sorted sites }

/-- How many open sites report the same failure as `s` (`Site.sameAs`). -/
def Open.count (os : List Open) (s : Site) : Nat := (os.filter (·.site.sameAs s)).length

/-- The edit removed one instance of the head's failure, and every failure it
added lies after the edit, in the attempted site's declaration
(`docs/parallel.md` X4). `old` are the open sites before the edit, the head
included; `sites` are the open sites after it. A site is new when its failure
occurs more often after the edit than before. Lean checks each declaration on
its own, so an error that the edit exposes can only be in the edited
declaration, after the bytes the edit changed. An error inside those bytes is
the edit's own failure. A new error in another declaration is a break that
the edit caused. EVMLean run 21 committed `closeBullet "omega"` four times in
`AccountLocality`: `omega` failed inside its own bytes, and the shorter text
made that error look later. -/
def Candidate.leavesOnlyLater (c : Candidate) (head : Site) (old sites : List Open) : Bool :=
  let spans := if c.changed.isEmpty then [(c.start, c.start + c.replacement.utf8ByteSize)]
    else c.changed
  let after (s : Site) : Bool :=
    spans.all fun (x, y) => !(decide (x ≤ s.start)) || decide (y ≤ s.start)
  decide (Open.count sites head < Open.count old head) &&
    sites.all fun o =>
      decide (Open.count sites o.site ≤ Open.count old o.site) ||
        (o.site.decl.isSome && o.site.decl == head.decl && after o.site)

/-- The transition function (`docs/machine.md` § Transitions, `docs/parallel.md`
X1-X8).

* `attempt` then `rebuilt`: accept if the edit made progress, the candidate is
  clean, and it caused no linter warning. Progress is the earliest open
  position moving strictly toward the end of the file: a later declaration,
  or the same declaration with a smaller `Site.reach` (X3). The Core sorts
  every open site the shell reports, in source-position order, not the
  shell's message order (`Mending.sortOpens`, X2); the new head is the
  earliest of them, so any number of later errors in the attempted site's
  declaration may appear and still be accepted. The edit must also remove
  one instance of the head's failure and add failures only after its own
  bytes in the attempted site's declaration (`Candidate.leavesOnlyLater`,
  X4); otherwise reject. If the edit made
  progress and every warning is an unused simp argument, Lean's own hint
  makes the better candidate: the same edit without those arguments replaces
  the head candidate, and the shell attempts it next. A flagged candidate is
  never accepted. Otherwise reject (`docs/rules.md` § Entrenchment and order).
* `attempt` then `unparsable`: reject.
* `giveUp` then `gaveUp`: the head site becomes residue.

Any other pair is an observation that does not fit the state. -/
def Mending.step (m : Mending) (o : MendObs) : Except Refusal Mending :=
  match hs : m.sites, o with
  | o₀ :: _rest, .gaveUp =>
    if o₀.candidates.isEmpty then .ok (m.giveUp hs)
    else .error (.observationMismatch "gaveUp with candidates left")
  | o₀ :: _rest, .unparsable =>
    if o₀.candidates.isEmpty then .error (.observationMismatch "no candidate was attempted")
    else .ok (m.reject hs)
  | o₀ :: _rest, .rebuilt e lint unused sites =>
    match o₀.candidates with
    | [] => .error (.observationMismatch "no candidate was attempted")
    | c :: _ =>
      if hBound : ∀ o ∈ sites, o.site.declIndex < m.decls then
        if c.leavesOnlyLater o₀.site m.sites sites then
          if hp : o₀.site.declIndex < (Mending.afterCoord o₀ sites).1 ∨
              (o₀.site.declIndex = (Mending.afterCoord o₀ sites).1 ∧
                (Mending.afterCoord o₀ sites).2 < o₀.site.reach) then
            if hclean : c.clean = true ∧ lint = 0 then
              if hwf : (Mending.sortOpens sites).length + m.residue.length ≤ e then
                .ok (m.accept hs c e lint sites hBound hp hclean hwf)
              else .error (.observationMismatch "more open sites than errors")
            else
              -- Lean's hint: the same edit without the unused simp arguments. Only
              -- for an edit of one node (a file-wide edit has `changed` spans).
              if c.clean && lint > 0 && unused.length == lint && c.changed.isEmpty then
                match dropSimpArgs c.replacement unused with
                | some r =>
                  if r.length < c.replacement.length then
                    .ok (m.refine hs { c with
                      rule := s!"{c.rule} (Lean's hint: without {unused})"
                      replacement := r })
                  else .ok (m.reject hs)
                | none => .ok (m.reject hs)
              else .ok (m.reject hs)
          else .ok (m.reject hs)
        else .ok (m.reject hs)
      else .error (.observationMismatch "a reported site names a declaration outside the module")
  | [], _ => .error (.observationMismatch "no open site")

/-- `Mending.step` never changes which module it mends: `giveUp`, `reject`,
`accept` and `refine` all keep the original `module` field. A `Fleet`
(`docs/parallel.md` § Level 2) relies on this to route an observation to one
member and still know the result carries the same module name. -/
theorem Mending.step_module (m m' : Mending) (o : MendObs) (h : m.step o = .ok m') :
    m'.module = m.module := by
  unfold Mending.step at h
  split at h
  · rename_i o₀ rest hs
    split at h
    · cases h; rfl
    · cases h
  · rename_i o₀ rest hs
    split at h
    · cases h
    · cases h; rfl
  · rename_i o₀ rest e lint unused sites hs
    split at h
    · cases h
    · rename_i c cs hc
      split at h
      · split at h  -- the exposure guard
        · split at h
          · split at h
            · split at h
              · cases h; rfl
              · cases h
            · split at h
              · split at h
                · split at h
                  · cases h; rfl
                  · cases h; rfl
                · cases h; rfl
              · cases h; rfl
          · cases h; rfl
        · cases h; rfl
      · cases h
  · cases h

/-- The termination measure inside `Mending` (`docs/parallel.md` X5, widened
by one component): the declarations after the head, then the head site's
`Site.reach` (an exposing edit lowers it), then the number of open sites (a
`giveUp` always lowers it, even when the position and the candidate count of
the newly-exposed head do not — the head may tie the position it replaces),
then the candidates left at the head site, then the length of the head
candidate's replacement (a cleaning shortens it). -/
def Mending.measure (m : Mending) : Nat × Nat × Nat × Nat × Nat :=
  match m.sites with
  | [] => (0, 0, m.sites.length, 0, 0)
  | o :: _ =>
    (m.decls - 1 - o.site.declIndex, o.site.reach, m.sites.length, o.candidates.length,
     (o.candidates.head?.map (·.replacement.length)).getD 0)

/-! ## Level 3: inside `FindingMending` -/

/-- An open finding-site and the candidates still to try, in rule order. The
state holds what is left, not what was tried (concept B6), the same shape
`Open` gives a diagnostic's site (`docs/machine.md` § `FindingMending`). -/
structure OpenFindingSite where
  group : FindingSiteGroup
  candidates : List Candidate
  deriving Repr

/-- An accepted repair at one finding site (`docs/machine.md` § Acceptance):
it carries the evidence that the three acceptance conditions held, the same
way `Accepted` carries a diagnostic repair's evidence. -/
structure FindingAccepted where
  candidate : Candidate
  site : SiteKey
  /-- Condition 1: every finding this site closes now has its baseline axiom
  set, in the site's module and in every rebuilt importer. -/
  baselineRestored : Bool
  /-- Condition 2: no declaration of the site's module, and no rebuilt
  importer, has a new finding of any kind. -/
  noNewFinding : Bool
  /-- Condition 3: the site's module, and every rebuilt importer, still
  build with no new error. -/
  stillBuilds : Bool
  conditionsHeld : baselineRestored = true ∧ noNewFinding = true ∧ stillBuilds = true
  /-- The findings the repair closes: the accepted site's whole group
  (`docs/machine.md` § Acceptance condition 1 closes every one of them). -/
  closed : List (String × String × List String)
  closedNonempty : closed ≠ []
  deriving Repr

/-- The state of one repair-frontier module (`docs/machine.md` § Level 3,
`FindingMending`): a module that owns the site of at least one open
finding. Sibling of `Mending`. -/
structure FindingMending where
  module : String
  sites : List OpenFindingSite
  /-- Site declarations whose candidates ran out in an earlier repair round
  (`docs/machine.md` § Termination, Level 3): once a site is exhausted it is
  never diagnosed again. -/
  exhausted : List String
  accepted : List FindingAccepted
  /-- Every open site closes at least one finding: `groupFindingSites` never
  builds an empty group. -/
  nonempty : ∀ o ∈ sites, o.group.members ≠ []
  deriving Repr

/-- What the shell must do next. -/
inductive FindingAction where
  /-- Apply this candidate in an attempt worktree and rebuild the site's
  module (`docs/machine.md` § Acceptance). -/
  | attempt (g : FindingSiteGroup) (c : Candidate)
  /-- The head site has no candidate left. -/
  | giveUp (g : FindingSiteGroup)
  /-- No open site is left. -/
  | finish

def FindingMending.next (m : FindingMending) : FindingAction :=
  match m.sites with
  | [] => .finish
  | o :: _ =>
    match o.candidates with
    | [] => .giveUp o.group
    | c :: _ => .attempt o.group c

/-- What the shell saw, attempting the head site's head candidate. -/
inductive FindingObs where
  /-- Acceptance conditions 1 to 3 all held (`docs/machine.md` §
  Acceptance): the shell's own rebuild, walk and `compare`, each reduced to
  its verdict. -/
  | accepted (baselineRestored noNewFinding stillBuilds : Bool)
  /-- One of the three conditions failed. -/
  | rejected
  /-- The head site had no candidate left. -/
  | gaveUp

/-- Changing a site's candidates keeps every site's group the same, so a
nonempty-group fact on the old list transfers to the new one. -/
theorem OpenFindingSite.nonempty_setCandidates {o : OpenFindingSite} {rest : List OpenFindingSite}
    (cs : List Candidate) (h : ∀ x ∈ o :: rest, x.group.members ≠ []) :
    ∀ x ∈ { o with candidates := cs } :: rest, x.group.members ≠ [] := by
  intro x hx
  rcases List.mem_cons.mp hx with hx | hx
  · subst hx; exact h o (List.mem_cons_self ..)
  · exact h x (List.mem_cons_of_mem _ hx)

/-- Reject the head candidate of the head site: drop it, in place. Takes the
split of `m.sites` explicitly, as `Mending.reject` does. -/
def FindingMending.reject (m : FindingMending) {o₀ : OpenFindingSite} {rest : List OpenFindingSite}
    (hs : m.sites = o₀ :: rest) : FindingMending :=
  { m with
    sites := { o₀ with candidates := o₀.candidates.drop 1 } :: rest
    nonempty := OpenFindingSite.nonempty_setCandidates _ (hs ▸ m.nonempty) }

/-- Give up on the head site: it leaves `sites` and its declaration joins
`exhausted` (`docs/machine.md` § Termination, Level 3). -/
def FindingMending.giveUp (m : FindingMending) {o₀ : OpenFindingSite} {rest : List OpenFindingSite}
    (hs : m.sites = o₀ :: rest) : FindingMending :=
  { m with
    sites := rest
    exhausted := o₀.group.key.site.1 :: m.exhausted
    nonempty := fun x hx => m.nonempty x (hs ▸ List.mem_cons_of_mem _ hx) }

/-- Accept an attempt: close every finding the head site's group holds, and
commit the patch. Takes the split of `m.sites` explicitly and the three
acceptance conditions as a conjunction, carried on the `FindingAccepted`
record (`docs/machine.md` § Acceptance). -/
def FindingMending.accept (m : FindingMending) {o₀ : OpenFindingSite} {rest : List OpenFindingSite}
    (hs : m.sites = o₀ :: rest) (c : Candidate)
    (baselineRestored noNewFinding stillBuilds : Bool)
    (hAccept : baselineRestored = true ∧ noNewFinding = true ∧ stillBuilds = true) :
    FindingMending :=
  { m with
    sites := rest
    accepted :=
      { candidate := c, site := o₀.group.key, baselineRestored, noNewFinding, stillBuilds,
        conditionsHeld := hAccept, closed := o₀.group.members,
        closedNonempty := m.nonempty o₀ (hs ▸ List.mem_cons_self ..) } :: m.accepted
    nonempty := fun x hx => m.nonempty x (hs ▸ List.mem_cons_of_mem _ hx) }

/-- The transition function (`docs/machine.md` § Level 3, § Acceptance).

* `attempt` then `accepted`: accept only when all three acceptance
  conditions held; otherwise the observation does not fit (the shell must
  report `rejected` instead).
* `attempt` then `rejected`: drop the head candidate.
* `giveUp` then `gaveUp`: the head site leaves `sites` for `exhausted`.

Any other pair is an observation that does not fit the state. -/
def FindingMending.step (m : FindingMending) (o : FindingObs) : Except Refusal FindingMending :=
  match hs : m.sites, o with
  | o₀ :: _rest, .gaveUp =>
    if o₀.candidates.isEmpty then .ok (m.giveUp hs)
    else .error (.observationMismatch "gaveUp with candidates left")
  | o₀ :: _rest, .rejected =>
    if o₀.candidates.isEmpty then .error (.observationMismatch "no candidate was attempted")
    else .ok (m.reject hs)
  | o₀ :: _rest, .accepted baselineRestored noNewFinding stillBuilds =>
    match o₀.candidates with
    | [] => .error (.observationMismatch "no candidate was attempted")
    | c :: _ =>
      if h : baselineRestored = true ∧ noNewFinding = true ∧ stillBuilds = true then
        .ok (m.accept hs c baselineRestored noNewFinding stillBuilds h)
      else .error (.observationMismatch "an acceptance condition failed")
  | [], _ => .error (.observationMismatch "no open site")

/-- `FindingMending.step` never changes which module it repairs: `giveUp`,
`reject` and `accept` all keep the original `module` field. `Fleet3`
(`docs/machine.md` § Level 3) relies on this to route an observation to one
member and still know the result carries the same module name, the same way
`Fleet` relies on `Mending.step_module`. -/
theorem FindingMending.step_module (m m' : FindingMending) (o : FindingObs)
    (h : m.step o = .ok m') : m'.module = m.module := by
  unfold FindingMending.step at h
  split at h
  · rename_i o₀ rest hs
    split at h
    · cases h; rfl
    · cases h
  · rename_i o₀ rest hs
    split at h
    · cases h
    · cases h; rfl
  · rename_i o₀ rest baselineRestored noNewFinding stillBuilds hs
    split at h
    · cases h
    · rename_i c cs _hc
      split at h
      · cases h; rfl
      · cases h
  · cases h

/-- The Level 3 measure's first item (`docs/machine.md` § Termination):
the open findings at a site still in `sites`. `accept` and `giveUp` both
remove the head site from `sites`, so both lower this item by the site's own
finding count; `reject` leaves `sites` the same length, so it does not
change. -/
def FindingMending.openFindingCount (m : FindingMending) : Nat :=
  (m.sites.map (·.group.members.length)).sum

/-- The Level 3 measure's second item: the candidates left, summed over
every open site. -/
def FindingMending.candidatesLeft (m : FindingMending) : Nat :=
  (m.sites.map (·.candidates.length)).sum

/-- The termination measure inside `FindingMending`
(`docs/machine.md` § Termination, Level 3): `(openFindingCount,
candidatesLeft)`, lexicographic. -/
def FindingMending.measure (m : FindingMending) : Nat × Nat :=
  (m.openFindingCount, m.candidatesLeft)

end LeanMend
