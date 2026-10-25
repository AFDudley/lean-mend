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

/-- Drop the head candidate of the head site. -/
def Mending.reject (m : Mending) : Mending :=
  match h : m.sites with
  | [] => m
  | o :: rest =>
    { m with
      sites := { o with candidates := o.candidates.drop 1 } :: rest
      wf := by have := m.wf; simp_all }

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

/-- Replace the head candidate of the head site with its cleaned form. -/
def Mending.refine (m : Mending) (c' : Candidate) : Mending :=
  match h : m.sites with
  | [] => m
  | o :: rest =>
    { m with
      sites := { o with candidates := c' :: o.candidates.drop 1 } :: rest
      wf := by have := m.wf; simp_all }

/-- The same failure after an edit elsewhere in the file: byte positions
move, so a site is identified by its declaration, class and message. -/
def Site.sameAs (a b : Site) : Bool :=
  a.decl == b.decl && a.diagnostic.kind == b.diagnostic.kind && a.diagnostic.text == b.diagnostic.text

/-- The one site that the edit exposed, if there is one (`Candidate.exposes`). The new open sites
hold exactly one site that matches no other old site (`Site.sameAs`; `others`
are the old open sites without the attempted one). That site is in the
attempted site's declaration, after every byte the edit changed there, and
nearer the declaration's end (`Site.reach`). The shell reports sites in
Lean's message order, not source order, so the check reads every site, not
the head. A changed span in a later declaration cannot change this one. -/
def Candidate.exposedSite (c : Candidate) (s : Site) (others sites : List Open) : Option Open :=
  let spans := if c.changed.isEmpty then [(c.start, c.start + c.replacement.utf8ByteSize)]
    else c.changed
  match sites.filter (fun o => !others.any (·.site.sameAs o.site)) with
  | [o'] =>
    match o'.site.declText with
    | none => none
    | some (a, t) =>
      if o'.site.decl.isSome && o'.site.decl == s.decl &&
          spans.all (fun (x, y) => decide (a + t.utf8ByteSize ≤ x) || decide (y ≤ o'.site.start))
      then some o' else none
  | _ => none

@[inherit_doc Candidate.exposedSite]
def Candidate.exposes (c : Candidate) (s : Site) (others sites : List Open) : Option Open :=
  (c.exposedSite s others sites).filter fun o' => decide (o'.site.reach < s.reach)

theorem Candidate.exposes_reach {c : Candidate} {s : Site} {others sites : List Open} {o' : Open}
    (h : c.exposes s others sites = some o') : o'.site.reach < s.reach := by
  unfold Candidate.exposes at h
  cases hx : c.exposedSite s others sites with
  | none => simp [hx] at h
  | some o =>
    rw [hx] at h
    simp only [Option.filter] at h
    split at h <;> simp_all

/-- The new open sites, with the exposed site first: the next attempt is at the
error the edit exposed. -/
def Candidate.reorder (x : Option Open) (sites : List Open) : List Open :=
  match x with
  | some o' => o' :: sites.filter (fun o => !(o.site.sameAs o'.site))
  | none => sites

/-- The transition function (`docs/machine.md` § Transitions).

* `attempt` then `rebuilt`: accept if the edit made progress, the candidate is
  clean, and it caused no linter warning. Progress is a fall in the error
  count, or an unchanged count where the edit exposed one later error of the
  same declaration (`Candidate.exposes`); the exposed site becomes the head
  site. If the edit made progress and every
  warning is an unused simp argument, Lean's own hint makes the better
  candidate: the same edit without those arguments replaces the head
  candidate, and the shell attempts it next. A flagged candidate is never
  accepted. Otherwise reject (`docs/rules.md` § Entrenchment and order).
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
  | o₀ :: _, .rebuilt e lint unused sites =>
    match o₀.candidates with
    | [] => .error (.observationMismatch "no candidate was attempted")
    | c :: _ =>
      -- `e` is the module's whole error count, residue sites included, so it
      -- is compared with unresolved plus residue.
      if hp : e < m.errors + m.residue.length ∨
          (e = m.errors + m.residue.length ∧ (c.exposes o₀.site (m.sites.drop 1) sites).isSome) then
        if hclean : c.clean = true ∧ lint = 0 then
          if hwf : (Candidate.reorder (c.exposes o₀.site (m.sites.drop 1) sites) sites).length + m.residue.length ≤ e then
            .ok { m with
              errors := e - m.residue.length
              sites := Candidate.reorder (c.exposes o₀.site (m.sites.drop 1) sites) sites
              accepted :=
                { candidate := c, errorsBefore := m.errors + m.residue.length, errorsAfter := e,
                  reachBefore := o₀.site.reach,
                  reachAfter := ((Candidate.reorder (c.exposes o₀.site (m.sites.drop 1) sites) sites).head?.map (·.site.reach)).getD 0,
                  progress := by
                    rcases hp with h | ⟨h1, h2⟩
                    · exact Or.inl h
                    · refine Or.inr ⟨h1, ?_⟩
                      match hx : c.exposes o₀.site (m.sites.drop 1) sites, h2 with
                      | some o', _ =>
                        simp only [Candidate.reorder, List.head?_cons, Option.map_some,
                          Option.getD_some]
                        exact Candidate.exposes_reach hx
                  clean := hclean.1, lintAtEdit := lint, lintFree := hclean.2 } :: m.accepted
              wf := by omega }
          else .error (.observationMismatch "more open sites than errors")
        else
          -- Lean's hint: the same edit without the unused simp arguments. Only
          -- for an edit of one node (a file-wide edit has `changed` spans).
          if c.clean && lint > 0 && unused.length == lint && c.changed.isEmpty then
            match dropSimpArgs c.replacement unused with
            | some r =>
              if r.length < c.replacement.length then
                .ok (m.refine { c with
                  rule := s!"{c.rule} (Lean's hint: without {unused})"
                  replacement := r })
              else .ok m.reject
            | none => .ok m.reject
          else .ok m.reject
      else .ok m.reject
  | [], _ => .error (.observationMismatch "no open site")

/-- The termination measure inside `Mending` (`docs/machine.md` § Termination):
the unresolved errors, then the head site's `Site.reach` (an exposing edit
lowers it), then the candidates left at the head site, then the length of the
head candidate's replacement (a cleaning shortens it). -/
def Mending.measure (m : Mending) : Nat × Nat × Nat × Nat :=
  (m.errors, (m.sites.head?.map (·.site.reach)).getD 0,
   (m.sites.head?.map (·.candidates.length)).getD 0,
   ((m.sites.head?.bind (·.candidates.head?)).map (·.replacement.length)).getD 0)

end LeanMend
