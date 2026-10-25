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

/-- The transition function (`docs/machine.md` § Transitions).

* `attempt` then `rebuilt`: accept if the error count fell, the candidate is
  clean, and it caused no linter warning. If the error count fell and every
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
      if hfell : e < m.errors + m.residue.length then
        if hclean : c.clean = true ∧ lint = 0 then
          if hwf : sites.length + m.residue.length ≤ e then
            .ok { m with
              errors := e - m.residue.length
              sites := sites
              accepted :=
                { candidate := c, errorsBefore := m.errors + m.residue.length, errorsAfter := e,
                  fell := hfell, clean := hclean.1, lintAtEdit := lint,
                  lintFree := hclean.2 } :: m.accepted
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

/-- The same failure after an edit elsewhere in the file: byte positions
move, so a site is identified by its declaration, class and message. -/
def Site.sameAs (a b : Site) : Bool :=
  a.decl == b.decl && a.diagnostic.kind == b.diagnostic.kind && a.diagnostic.text == b.diagnostic.text

/-- The termination measure inside `Mending` (`docs/machine.md` § Termination):
the unresolved errors, then the candidates left at the head site, then the
length of the head candidate's replacement (a cleaning shortens it). -/
def Mending.measure (m : Mending) : Nat × Nat × Nat :=
  (m.errors, (m.sites.head?.map (·.candidates.length)).getD 0,
   ((m.sites.head?.bind (·.candidates.head?)).map (·.replacement.length)).getD 0)

end LeanMend
