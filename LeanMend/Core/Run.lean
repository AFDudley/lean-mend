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

/-- Failing modules whose imports all build (`docs/glossary.md`, frontier). -/
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

/-- A set of concurrent `Mending` states, one per module of the current
wave (`docs/parallel.md` § Level 2: parallel frontier modules). -/
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

/-- The level-1 states. Each holds exactly what `docs/machine.md` lists for
it, so a state without its data cannot be built (concept B1). -/
inductive RunState where
  | idle (target : String)
  | baselined (target : String) (base : Certificate)
  | built (c : Context) (st : Statuses)
  | mending (c : Context) (st : Statuses) (f : Fleet)
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
  /-- The after certificate. -/
  | certificate (after : Certificate)
  | judgment (j : Judgment)

/-- `compare`, then the next state: `done`, `awaiting` or a refusal. -/
def RunState.close (c : Context) (after : Certificate) (residue : List String)
    (js : List Judgment) : RunState :=
  let fs := compare c.aliases c.base after js
  match fs.find? (·.reason.card.isNone) with
  | some f => .halted (.invariantBroken f.decl.module)
  | none => if fs.isEmpty then .done c after residue js else .awaiting c after residue js fs

def RunState.step : RunState → RunObs → RunState
  | .idle t, .baseline cert failing =>
    if failing.isEmpty then .baselined t cert else .halted (.baselineRed failing)
  | .baselined t base, .bumped mods aliases =>
    match aliases.resolve with
    | none => .halted (.aliasCycle "alias map")
    | some a => .built ⟨t, base, mods, a⟩ (fun _ => .blocked)
  | .built c st, .build st' =>
    if decide (Settled c.mods st st') then .built c st'
    else .halted (.observationMismatch "a closed module changed status")
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
  | .built c st, .certificate after =>
    if (frontier c.mods st).isEmpty then
      let residue := c.mods.filterMap fun m =>
        if st m.name == .built then none else some m.name
      RunState.close c after residue []
    else .halted (.observationMismatch "certificate taken with a frontier left")
  | .awaiting c after residue js open_, .judgment j =>
    if open_.any (c.aliases.rename ·.decl.name == j.subject) then
      RunState.close c after residue (j :: js)
    else .halted (.unknownCard j.card)
  | _, _ => .halted (.observationMismatch "observation does not fit the state")

/-- The state's name, for reports and tests. -/
def RunState.tag : RunState → String
  | .idle .. => "idle" | .baselined .. => "baselined" | .built .. => "built"
  | .mending .. => "mending" | .awaiting .. => "awaiting" | .done .. => "done"
  | .halted r => s!"halted {repr r}"

end LeanMend
