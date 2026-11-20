import LeanMend.Core.Mend
import LeanMend.Core.Compare

/-!
# Level 1: the run

The run over modules (`docs/machine.md` § Level 1). Every function is pure.
The shell makes each observation, records it in the ledger, and calls
`RunState.step`.
-/

namespace LeanMend

/-- A module and its imports, from the probe's `imports` command. -/
structure Module where
  name : String
  imports : List String
  deriving Repr

inductive ModStatus where
  | built | failing | blocked | residual
  deriving DecidableEq, Repr

/-- A module the run still has to handle. -/
def ModStatus.isOpen : ModStatus → Bool
  | .failing | .blocked => true
  | .built | .residual => false

abbrev Statuses := String → ModStatus

/-- Failing modules whose imports all build (`glossary.md`, frontier). -/
def frontier (mods : List Module) (st : Statuses) : List String :=
  (mods.filter fun m => st m.name == .failing && m.imports.all (st · == .built)).map
    (·.name)

/-- Two different frontier modules never import each other: a module whose
imports all build cannot import another module that is still failing
(`docs/parallel.md` § Level 2: parallel frontier modules). The conclusion
names the module record `frontier` found for `m`, since that is the record
whose import list the claim is about. -/
theorem frontier_pairwise_indep (mods : List Module) (st : Statuses) (m n : String)
    (hm : m ∈ frontier mods st) (hn : n ∈ frontier mods st) (_hne : m ≠ n) :
    ∃ mm ∈ mods, mm.name = m ∧ n ∉ mm.imports := by
  simp only [frontier, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hm hn
  obtain ⟨mm, ⟨hmmem, _, hmbuilt⟩, hmname⟩ := hm
  obtain ⟨nn, ⟨_, hnfail, _⟩, hnname⟩ := hn
  refine ⟨mm, hmmem, hmname, fun hcontra => ?_⟩
  have hbuilt := hmbuilt n hcontra
  rw [hnname] at hnfail
  rw [hbuilt] at hnfail
  exact absurd hnfail (by decide)

/-- Every open module whose imports all build, in `mods` order: the dataflow
schedule (`docs/parallel.md` § Level 2, P8, P21). A `failing` one is ready to
mend, and a `blocked` one is ready to build. A module does not wait for a
module that it does not import. The head of the list is the next module of
the canonical sequential order (P10, P12). -/
def ready (mods : List Module) (st : Statuses) : List String :=
  (mods.filter fun m => (st m.name).isOpen && m.imports.all (st · == .built)).map (·.name)

/-- A ready module is open, and every module that it imports builds: the
dataflow start condition (`docs/parallel.md` P8). -/
theorem ready_imports_built (mods : List Module) (st : Statuses) (n : String)
    (h : n ∈ ready mods st) :
    ∃ m ∈ mods, m.name = n ∧ (st n).isOpen = true ∧ ∀ i ∈ m.imports, st i = .built := by
  simp only [ready, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨m, ⟨hm, hopen, himp⟩, rfl⟩ := h
  exact ⟨m, hm, rfl, hopen, himp⟩

/-- Every frontier module is ready: the frontier is the `failing` part of
`ready`. -/
theorem frontier_sub_ready (mods : List Module) (st : Statuses) (n : String)
    (h : n ∈ frontier mods st) : n ∈ ready mods st := by
  simp only [frontier, ready, List.mem_map, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h ⊢
  obtain ⟨m, ⟨hm, hfail, himp⟩, rfl⟩ := h
  exact ⟨m, ⟨hm, by simp [hfail, ModStatus.isOpen], himp⟩, rfl⟩

def openCount (mods : List Module) (st : Statuses) : Nat :=
  mods.countP fun m => (st m.name).isOpen

/-- The status of one module, set when it leaves `Mending`. -/
def finish (st : Statuses) (name : String) (s : ModStatus) : Statuses :=
  fun n => if n = name then s else st n

/-- A rebuild keeps every closed module closed and as it was. A built module
that fails again is an observation the machine refuses. -/
def Settled (mods : List Module) (st st' : Statuses) : Prop :=
  ∀ m ∈ mods, (st m.name).isOpen = false → st' m.name = st m.name

instance (mods : List Module) (st st' : Statuses) : Decidable (Settled mods st st') := by
  unfold Settled; infer_instance

/-- Resolve a chain `a → b → c` to `a → c`. `none` means a cycle. A chain has
at most `pairs.length` links, so that bound is the fuel. -/
def AliasMap.resolve (m : AliasMap) : Option AliasMap := do
  let rec follow (fuel : Nat) (n : String) : Option String :=
    match m.pairs.lookup n with
    | none => some n
    | some n' => match fuel with
      | 0 => none
      | fuel + 1 => follow fuel n'
  let pairs ← m.pairs.mapM fun (a, b) => (a, ·) <$> follow m.pairs.length b
  pure ⟨pairs⟩

/-- What every state after `Bumped` knows. -/
structure Context where
  target : String
  base : Certificate
  mods : List Module
  aliases : AliasMap
  /-- Site declarations whose candidate list ran out in an earlier repair
  round (`docs/machine.md` § Termination, Level 3): the `certificate`
  guard for `repairing` excludes them, so a site that already gave up is
  never diagnosed for a candidate again, even across repair rounds. -/
  exhaustedSites : List String := []

/-- A set of concurrent `Mending` states, one per module (`docs/parallel.md`
§ Level 2). The driver replays one module at a time in the canonical order,
so its ledger fills the fleet with one member at a time. -/
structure Fleet where
  mendings : List Mending
  /-- Two members never mend the same module, so a module name picks out
  at most one of them. -/
  distinct : (mendings.map (·.module)).Nodup

/-- The member of `f` mending `name`, if any. -/
def Fleet.find? (f : Fleet) (name : String) : Option Mending :=
  f.mendings.find? (·.module == name)

/-- The member `Fleet.find?` returns is the one named by the query. -/
theorem Fleet.find?_some {f : Fleet} {name : String} {m : Mending}
    (h : f.find? name = some m) : m.module = name := by
  have h' := List.find?_some h
  exact beq_iff_eq.mp h'

/-- `f` with no member mending `name`: dropping members only ever shrinks
`f.mendings`, so it keeps the module-name list distinct. -/
def Fleet.remove (f : Fleet) (name : String) : Fleet :=
  { mendings := f.mendings.filter (·.module != name)
    distinct := List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) f.distinct }

/-- Add a new member mending `name`, when the fleet does not already have
one. -/
def Fleet.add (f : Fleet) (m : Mending) (h : m.module ∉ f.mendings.map (·.module)) : Fleet :=
  { mendings := m :: f.mendings, distinct := List.nodup_cons.mpr ⟨h, f.distinct⟩ }

/-- Replacing the member named `name` by `m'`, itself named `name`, leaves
the module-name list exactly as it was: the proof `Fleet.step` needs for its
own well-formedness, and the content behind `Fleet.step_wf` below. -/
private theorem Fleet.step_names (l : List Mending) (name : String) (m' : Mending)
    (hm' : m'.module = name) :
    (l.map fun x => if x.module == name then m' else x).map (·.module) = l.map (·.module) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, ih]
    by_cases h : x.module == name
    · simp [hm', beq_iff_eq.mp h]
    · simp [h]

/-- Route `o` to the member mending `name`, and replace it in place. A
module name that is not in the fleet, or whose `Mending.step` refuses, halts
the run (`docs/parallel.md` § Level 2). -/
def Fleet.step (f : Fleet) (name : String) (o : MendObs) : Except Refusal Fleet :=
  match hf : f.find? name with
  | none => .error (.observationMismatch s!"{name} is not in the fleet")
  | some m =>
    match hm : m.step o with
    | .error r => .error r
    | .ok m' =>
      .ok { f with
        mendings := f.mendings.map fun x => if x.module == name then m' else x
        distinct :=
          Fleet.step_names f.mendings name m'
            ((Mending.step_module m m' o hm).trans (Fleet.find?_some hf)) ▸
            f.distinct }

/-- Routing an observation to its module changes that member's `Mending`
only, so the fleet's module set — and the distinctness it satisfies — is
exactly what it was before (`docs/parallel.md` § Level 2: parallel frontier
modules). -/
theorem Fleet.step_wf (f : Fleet) (name : String) (o : MendObs) (f' : Fleet)
    (h : Fleet.step f name o = .ok f') :
    f'.mendings.map (·.module) = f.mendings.map (·.module) := by
  unfold Fleet.step at h
  split at h
  · cases h
  · rename_i m hf
    split at h
    · cases h
    · rename_i m' hm
      cases h
      exact Fleet.step_names f.mendings name m'
        ((Mending.step_module m m' o hm).trans (Fleet.find?_some hf))

/-- A set of concurrent `FindingMending` states, one per repair-frontier
module (`docs/machine.md` § Level 3, `FindingMending`'s own "Fleet-shaped
collection"), mirroring `Fleet` for `Mending`. The driver repairs one
repair-frontier module at a time, in the order `buildFleet3` gives, so its
ledger fills the fleet with one member at a time, exactly as `Fleet` does
for Level 2. -/
structure Fleet3 where
  mendings : List FindingMending
  /-- Two members never repair the same module, so a module name picks out
  at most one of them. -/
  distinct : (mendings.map (·.module)).Nodup

/-- The member of `f` repairing `name`, if any. -/
def Fleet3.find? (f : Fleet3) (name : String) : Option FindingMending :=
  f.mendings.find? (·.module == name)

/-- The member `Fleet3.find?` returns is the one named by the query. -/
theorem Fleet3.find?_some {f : Fleet3} {name : String} {m : FindingMending}
    (h : f.find? name = some m) : m.module = name := by
  have h' := List.find?_some h
  exact beq_iff_eq.mp h'

/-- `f` with no member repairing `name`: dropping members only ever shrinks
`f.mendings`, so it keeps the module-name list distinct. -/
def Fleet3.remove (f : Fleet3) (name : String) : Fleet3 :=
  { mendings := f.mendings.filter (·.module != name)
    distinct := List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) f.distinct }

/-- Replacing the member named `name` by `m'`, itself named `name`, leaves
the module-name list exactly as it was: the proof `Fleet3.step` needs for
its own well-formedness, mirroring `Fleet.step_names`. -/
private theorem Fleet3.step_names (l : List FindingMending) (name : String) (m' : FindingMending)
    (hm' : m'.module = name) :
    (l.map fun x => if x.module == name then m' else x).map (·.module) = l.map (·.module) := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, ih]
    by_cases h : x.module == name
    · simp [hm', beq_iff_eq.mp h]
    · simp [h]

/-- Route `o` to the member repairing `name`, and replace it in place. A
module name that is not in the fleet, or whose `FindingMending.step`
refuses, halts the run (`docs/machine.md` § Level 3). -/
def Fleet3.step (f : Fleet3) (name : String) (o : FindingObs) : Except Refusal Fleet3 :=
  match hf : f.find? name with
  | none => .error (.observationMismatch s!"{name} is not in the repair fleet")
  | some m =>
    match hm : m.step o with
    | .error r => .error r
    | .ok m' =>
      .ok { f with
        mendings := f.mendings.map fun x => if x.module == name then m' else x
        distinct :=
          Fleet3.step_names f.mendings name m'
            ((FindingMending.step_module m m' o hm).trans (Fleet3.find?_some hf)) ▸
            f.distinct }

/-- Routing an observation to its module changes that member's
`FindingMending` only, so the fleet's module set — and the distinctness it
satisfies — is exactly what it was before (`docs/machine.md` § Level 3). -/
theorem Fleet3.step_wf (f : Fleet3) (name : String) (o : FindingObs) (f' : Fleet3)
    (h : Fleet3.step f name o = .ok f') :
    f'.mendings.map (·.module) = f.mendings.map (·.module) := by
  unfold Fleet3.step at h
  split at h
  · cases h
  · rename_i m hf
    split at h
    · cases h
    · rename_i m' hm
      cases h
      exact Fleet3.step_names f.mendings name m'
        ((FindingMending.step_module m m' o hm).trans (Fleet3.find?_some hf))

/-- One repair-frontier module's `FindingMending`, for the `repairing`
fleet (`docs/machine.md` § Level 3): the first module `sites`' head
names, holding every one of `sites` that belongs to it. The driver
repairs one repair-frontier module per `certificate` round, the same way
it mends one frontier module at a time at Level 2. `none` when `sites` is
empty, or when every site of `sites` has no candidate left: the
`built --> repairing` guard (`docs/machine.md` § Transitions) — "an open
finding's site has an unexhausted candidate". -/
def buildFleet3 (sites : List OpenFindingSite) (hne : ∀ o ∈ sites, o.group.members ≠ []) :
    Option Fleet3 :=
  if sites.all (·.candidates.isEmpty) then none else
  match sites.head? with
  | none => none
  | some hd =>
    let m := hd.group.key.site.2
    let os := sites.filter (·.group.key.site.2 == m)
    some { mendings :=
             [{ module := m, sites := os, exhausted := [], accepted := [],
                nonempty := fun o ho => hne o (List.mem_filter.mp ho).1 }]
           distinct := by simp }

/-- The level-1 states. Each holds exactly what `docs/machine.md` lists for
it, so a state without its data cannot be built (concept B1). -/
inductive RunState where
  | idle (target : String)
  | baselined (target : String) (base : Certificate)
  | built (c : Context) (st : Statuses)
  | mending (c : Context) (st : Statuses) (f : Fleet)
  /-- Level 3 (`docs/machine.md` § Level 3): the context, the statuses, the
  after certificate, the open findings, and one repair-frontier module as a
  `FindingMending` value in `f`. -/
  | repairing (c : Context) (st : Statuses) (after : Certificate) (open_ : List Finding) (f : Fleet3)
  | awaiting (c : Context) (after : Certificate) (residue : List String)
      (js : List Judgment) (open_ : List Finding)
  | done (c : Context) (after : Certificate) (residue : List String) (js : List Judgment)
  | halted (r : Refusal)

/-- What the shell saw. -/
inductive RunObs where
  /-- The baseline certificate and the modules that failed at the old toolchain. -/
  | baseline (cert : Certificate) (failing : List String)
  /-- The module graph and the raw alias pairs at the new toolchain. -/
  | bumped (mods : List Module) (aliases : AliasMap)
  /-- The status of every module after `lake build`. -/
  | build (st : Statuses)
  /-- The diagnostics of one frontier module, as open sites with candidates.
  `decls` is the module's declaration count (`docs/parallel.md` X6). -/
  | diagnosed (module : String) (decls : Nat) (sites : List Open)
  /-- One level-2 observation, for the named module's `Mending`. -/
  | mend (module : String) (o : MendObs)
  /-- The shell saw `Mending.next = .finish` and left the named module's
  `Mending`. -/
  | mended (module : String)
  /-- The status of one module after `lake build <module>`
  (`docs/parallel.md` P13, P21): a `blocked` module once every module it
  imports builds, or a module that the run mended with no residue. -/
  | moduleBuild (module : String) (status : ModStatus)
  /-- The after certificate, and the shell's Level 3 candidate groups
  (`docs/machine.md` § Level 3): one `OpenFindingSite` per `FindingSiteGroup`
  that `groupFindingSites` and `findingCandidates` give, already filtered to
  the sites `exhaustedSites` excludes. -/
  | certificate (after : Certificate) (sites3 : List OpenFindingSite)
  /-- One Level 3 observation, for the named module's `FindingMending`. -/
  | repair (module : String) (o : FindingObs)
  /-- The shell saw `FindingMending.next = .finish` and left the named
  module's `FindingMending`. -/
  | repaired (module : String)
  | judgment (j : Judgment)

/-- `compare`'s findings, or the first finding that breaks the invariant
(`docs/machine.md` § The invariant), shared by `RunState.close` and the
`certificate` transition, which also tries Level 3 before falling back to
`awaiting`. It runs `compareIx`, which `compareIx_eq` proves equal to
`compare`. -/
def RunState.compareClose (c : Context) (after : Certificate) (js : List Judgment) :
    Except Refusal (List Finding) :=
  let fs := compareIx (.of c.aliases after) c.base js
  match fs.find? (·.reason.card.isNone) with
  | some f => .error (.invariantBroken f.decl.module)
  | none => .ok fs

/-- `compare`, then the next state: `done`, `awaiting` or a refusal. -/
def RunState.close (c : Context) (after : Certificate) (residue : List String)
    (js : List Judgment) : RunState :=
  match RunState.compareClose c after js with
  | .error r => .halted r
  | .ok fs => if fs.isEmpty then .done c after residue js else .awaiting c after residue js fs

/-- The effect of one `moduleBuild name s` observation in `built`
(`docs/parallel.md` P13, P21). A `blocked` module that is `ready` takes its
build result, which must be `built` or `failing`: every module it imports
builds, so Lake cannot report it blocked again. A `built` module, which the
run just mended with no residue, must build. Any other observation halts. -/
def RunState.moduleBuilt (c : Context) (st : Statuses) (name : String) (s : ModStatus) :
    RunState :=
  match st name with
  | .blocked =>
    if name ∈ ready c.mods st ∧ (s = .built ∨ s = .failing) then .built c (finish st name s)
    else .halted (.observationMismatch s!"{name}: a module build that does not unblock it")
  | .built =>
    if s = .built then .built c st
    else .halted (.observationMismatch s!"{name}: a closed module changed status")
  | _ => .halted (.observationMismatch s!"{name}: a module build for a module that is not blocked or built")

/-- A `moduleBuild` keeps every closed module as it was, so
`openCount_settled` applies to it. -/
theorem RunState.moduleBuilt_settled (c c' : Context) (st st' : Statuses) (name : String)
    (s : ModStatus) (h : RunState.moduleBuilt c st name s = .built c' st') :
    c' = c ∧ Settled c.mods st st' := by
  unfold RunState.moduleBuilt at h
  split at h
  · rename_i hb
    split at h
    · cases h
      refine ⟨rfl, fun m _ hclosed => ?_⟩
      by_cases heq : m.name = name
      · simp [heq, hb, ModStatus.isOpen] at hclosed
      · simp [finish, heq]
    · cases h
  · split at h
    · cases h; exact ⟨rfl, fun _ _ _ => rfl⟩
    · cases h
  · cases h

def RunState.step : RunState → RunObs → RunState
  | .idle t, .baseline cert failing =>
    if failing.isEmpty then .baselined t cert else .halted (.baselineRed failing)
  | .baselined t base, .bumped mods aliases =>
    match aliases.resolve with
    | none => .halted (.aliasCycle "alias map")
    | some a => .built { target := t, base, mods, aliases := a } (fun _ => .blocked)
  | .built c st, .build st' =>
    if decide (Settled c.mods st st') then .built c st'
    else .halted (.observationMismatch "a closed module changed status")
  | .built c st, .moduleBuild name s => RunState.moduleBuilt c st name s
  | .built c st, .diagnosed name decls sites =>
    if name ∈ frontier c.mods st then
      if hBound : ∀ o ∈ sites, o.site.declIndex < decls then
        .mending c st
          { mendings :=
              [{ module := name, errors := sites.length, decls, sites := Mending.sortOpens sites,
                 residue := [], accepted := [],
                 wf := by simp [Mending.sortOpens_length]
                 bounded := Mending.sortOpens_bounded hBound
                 sorted := Mending.sortOpens_sorted sites }]
            distinct := by simp }
      else .halted (.observationMismatch s!"{name}: a site names a declaration outside the module")
    else .halted (.observationMismatch s!"{name} is not a frontier module")
  | .mending c st f, .diagnosed name decls sites =>
    if name ∈ frontier c.mods st then
      if hnew : name ∉ f.mendings.map (·.module) then
        if hBound : ∀ o ∈ sites, o.site.declIndex < decls then
          .mending c st (f.add
            { module := name, errors := sites.length, decls, sites := Mending.sortOpens sites,
              residue := [], accepted := [],
              wf := by simp [Mending.sortOpens_length]
              bounded := Mending.sortOpens_bounded hBound
              sorted := Mending.sortOpens_sorted sites }
            hnew)
        else .halted (.observationMismatch s!"{name}: a site names a declaration outside the module")
      else .halted (.observationMismatch s!"{name} is already in the fleet")
    else .halted (.observationMismatch s!"{name} is not a frontier module")
  | .mending c st f, .mended name =>
    match f.find? name with
    | none => .halted (.observationMismatch s!"{name} is not in the fleet")
    | some m =>
      match m.next with
      | .finish =>
        let st' := finish st name (if m.residue.isEmpty then .built else .residual)
        let f' := f.remove name
        if f'.mendings.isEmpty then .built c st' else .mending c st' f'
      | _ => .halted (.observationMismatch "open sites left in the module")
  | .mending c st f, .mend name o =>
    match Fleet.step f name o with
    | .ok f' => .mending c st f'
    | .error r => .halted r
  | .repairing c st after fs f, .repair name o =>
    match Fleet3.step f name o with
    | .ok f' => .repairing c st after fs f'
    | .error r => .halted r
  | .repairing c st after fs f, .repaired name =>
    match f.find? name with
    | none => .halted (.observationMismatch s!"{name} is not in the repair fleet")
    | some m =>
      match m.next with
      | .finish =>
        let c' := { c with exhaustedSites := c.exhaustedSites ++ m.exhausted }
        let f' := f.remove name
        if f'.mendings.isEmpty then .built c' st else .repairing c' st after fs f'
      | _ => .halted (.observationMismatch "open finding-sites left in the module")
  | .built c st, .certificate after sites3 =>
    if (frontier c.mods st).isEmpty then
      let residue := c.mods.filterMap fun m =>
        if st m.name == .built then none else some m.name
      if hne : ∀ o ∈ sites3, o.group.members ≠ [] then
        match RunState.compareClose c after [] with
        | .error r => .halted r
        | .ok fs =>
          if fs.isEmpty then .done c after residue []
          else
            match buildFleet3 sites3 hne with
            | some f3 => .repairing c st after fs f3
            | none => .awaiting c after residue [] fs
      else .halted (.observationMismatch "a Level 3 site group has no member")
    else .halted (.observationMismatch "certificate taken with a frontier left")
  | .awaiting c after residue js open_, .judgment j =>
    if open_.any (c.aliases.rename ·.decl.name == j.subject) then
      RunState.close c after residue (j :: js)
    else .halted (.unknownCard j.card)
  | _, _ => .halted (.observationMismatch "observation does not fit the state")

/-- The state's name, for reports and tests. -/
def RunState.tag : RunState → String
  | .idle .. => "idle" | .baselined .. => "baselined" | .built .. => "built"
  | .mending .. => "mending" | .repairing .. => "repairing" | .awaiting .. => "awaiting"
  | .done .. => "done" | .halted r => s!"halted {repr r}"

end LeanMend
