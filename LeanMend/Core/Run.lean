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

/-- The level-1 states. Each holds exactly what `docs/machine.md` lists for
it, so a state without its data cannot be built (concept B1). -/
inductive RunState where
  | idle (target : String)
  | baselined (target : String) (base : Certificate)
  | built (c : Context) (st : Statuses)
  | mending (c : Context) (st : Statuses) (m : Mending)
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
  /-- The diagnostics of one frontier module, as open sites with candidates. -/
  | diagnosed (module : String) (sites : List Open)
  /-- One level-2 observation. -/
  | mend (o : MendObs)
  /-- The shell saw `Mending.next = .finish` and left `Mending`. -/
  | mended
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
  | .built c st, .diagnosed name sites =>
    if name ∈ frontier c.mods st then
      .mending c st
        { module := name, errors := sites.length, sites := sites, residue := [],
          accepted := [], wf := Nat.le_refl _ }
    else .halted (.observationMismatch s!"{name} is not a frontier module")
  | .mending c st m, .mended =>
    match m.next with
    | .finish =>
      .built c (finish st m.module (if m.residue.isEmpty then .built else .residual))
    | _ => .halted (.observationMismatch "open sites left in the module")
  | .mending c st m, .mend o =>
    match m.step o with
    | .ok m' => .mending c st m'
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

end LeanMend
