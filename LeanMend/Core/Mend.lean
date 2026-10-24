import LeanMend.Spec.Types

/-!
# Level 2: inside `Mending`

One frontier module, its open sites and the candidates of the head site. See
`docs/machine.md` § Level 2. Every function here is pure. The shell makes the
observation, records it in the ledger, and then calls `Mending.step`.
-/

namespace LeanMend

/-- An open site and the candidates still to try, in rule order. The state
holds what is left, not what was tried (concept B6). -/
structure Open where
  site : Site
  candidates : List Candidate
  deriving Repr

/-- The state of one module in `Mending`. -/
structure Mending where
  module : String
  /-- Error sites in the module that are not marked residue. -/
  errors : Nat
  sites : List Open
  residue : List Site
  accepted : List Accepted
  /-- Each open site is one unresolved error. -/
  wf : sites.length ≤ errors

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
  /-- The module rebuilt with the candidate applied. `lint` counts the linter
  warnings (kind `linter.*`) inside the replaced bytes: warnings the candidate
  itself caused. `sites` are the open sites the shell read from the new
  diagnostics, with their candidates. -/
  | rebuilt (errors : Nat) (lint : Nat) (sites : List Open)
  /-- The shell recorded the head site as residue. -/
  | gaveUp

def Mending.next (m : Mending) : MendAction :=
  match m.sites with
  | [] => .finish
  | o :: _ =>
    match o.candidates with
    | [] => .giveUp o.site
    | c :: _ => .attempt c

/-- Drop the head candidate of the head site. -/
def Mending.reject (m : Mending) : Mending :=
  match h : m.sites with
  | [] => m
  | o :: rest =>
    { m with
      sites := { o with candidates := o.candidates.drop 1 } :: rest
      wf := by have := m.wf; simp_all }

/-- The transition function (`docs/machine.md` § Transitions).

* `attempt` then `rebuilt`: accept if the error count fell, the candidate is
  clean, and it caused no linter warning; otherwise reject. Candidate order is
  the rule author's preference among valid repairs; the linter condition
  rejects a candidate that Lean itself flags, for example an unused simp
  argument (`docs/rules.md` § Entrenchment and order).
* `attempt` then `unparsable`: reject.
* `giveUp` then `gaveUp`: the head site becomes residue.

Any other pair is an observation that does not fit the state. -/
def Mending.step (m : Mending) (o : MendObs) : Except Refusal Mending :=
  match hs : m.sites, o with
  | o₀ :: rest, .gaveUp =>
    if o₀.candidates.isEmpty then
      .ok { m with
        errors := m.errors - 1
        sites := rest
        residue := o₀.site :: m.residue
        wf := by have := m.wf; simp_all; omega }
    else .error (.observationMismatch "gaveUp with candidates left")
  | o₀ :: _, .unparsable =>
    if o₀.candidates.isEmpty then .error (.observationMismatch "no candidate was attempted")
    else .ok m.reject
  | o₀ :: _, .rebuilt e lint sites =>
    match o₀.candidates with
    | [] => .error (.observationMismatch "no candidate was attempted")
    | c :: _ =>
      if hfell : e < m.errors then
        if hclean : c.clean = true ∧ lint = 0 then
          if hwf : sites.length ≤ e then
            .ok { m with
              errors := e
              sites := sites
              accepted :=
                { candidate := c, errorsBefore := m.errors, errorsAfter := e,
                  fell := hfell, clean := hclean.1, lintAtEdit := lint,
                  lintFree := hclean.2 } :: m.accepted
              wf := hwf }
          else .error (.observationMismatch "more open sites than errors")
        else .ok m.reject
      else .ok m.reject
  | [], _ => .error (.observationMismatch "no open site")

/-- The termination measure inside `Mending` (`docs/machine.md` § Termination):
the unresolved errors, then the candidates left at the head site. -/
def Mending.measure (m : Mending) : Nat × Nat :=
  (m.errors, (m.sites.head?.map (·.candidates.length)).getD 0)

end LeanMend
