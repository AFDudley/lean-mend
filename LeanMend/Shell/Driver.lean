import LeanMend.Core.Propose
import LeanMend.Shell.Target

/-!
# The driver

The composition root (concept A3): the only module that knows both the machine
(`RunState.step`, `Mending.next`) and the adapters (`Shell.Target`). It makes
each observation, appends it to the ledger, and calls the pure transition.
See `docs/machine.md` and `docs/architecture.md`.

`lean-mend run <target> --adopt` handles a target that another tool already
bumped: the baseline is the parent commit (`HEAD~1`), checked out in a
detached worktree under `<target>/.lean-mend/base`. The mend branch is
`lean-mend/mend`, created at `HEAD`. Each accepted patch is one commit on it.

Not built yet: attempts in separate worktrees (concept D3). Attempts run in
the target checkout, one at a time, and a rejected candidate is reverted by
restoring the file's previous bytes.
-/

namespace LeanMend.Shell

open System (FilePath)
open Lean (Json toJson)

structure Ctx where
  target : FilePath
  toolchain : String
  /-- Every target module with its file, at `HEAD`. -/
  files : List (Module × FilePath)
  order : List Module
  /-- Lake targets to build; empty means the default targets. -/
  targets : List String
  aliases : AliasMap
  ledger : FilePath

def Ctx.fileOf (c : Ctx) (module : String) : FilePath :=
  ((c.files.find? (·.1.name == module)).map (·.2)).getD module

/-- Append one ledger line (concept D1): the observation and the next state. -/
def record (c : Ctx) (obs : String) (detail : Json) (next : RunState) : IO Unit := do
  let h ← IO.FS.Handle.mk c.ledger .append
  h.putStrLn <| Json.compress <| Json.mkObj
    [("obs", toJson obs), ("detail", detail), ("state", toJson next.tag)]

def stepL (c : Ctx) (s : RunState) (obs : RunObs) (name : String) (detail : Json := Json.null) :
    IO RunState := do
  let next := s.step obs
  record c name detail next
  pure next

/-- Statuses as the machine sees them: the shell's build result, except that a
module the machine closed as `residual` stays `residual`. -/
def overlay (machine : Statuses) (built : List (String × ModStatus)) : Statuses :=
  fun n => if machine n == .residual then .residual else (built.lookup n).getD .built

def statusList (c : Ctx) (st : Statuses) : List (String × ModStatus) :=
  c.order.map fun m => (m.name, st m.name)

def git (target : FilePath) (args : Array String) : IO String := runOk target "git" args

/-- Every alias pair from the probe's `deprecated`, in `project`, over `modules`. -/
def deprecated (project : FilePath) (modules : List String) : IO (List (String × String)) := do
  if modules.isEmpty then return []
  let out ← probe project (#["deprecated"] ++ modules.toArray)
  let rows ← parseOrThrow s!"probe deprecated in {project}" (Parse.lines Parse.alias_ out)
  pure (rows.filterMap id)

/-- The modules a project builds, for `--aliases-from`. -/
def projectModules (project : FilePath) : IO (List String) := do
  let mods ← moduleGraph project
  let order ← match topoOrder (mods.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{project}: {repr r}"
  let (inRun, st) ← buildAll project [] order
  if let some (m, _) := st.find? (·.2 != .built) then
    throw <| IO.userError s!"{project}: module {m} does not build"
  pure (inRun.map (·.name))

/-- The level-1 loop, after `bumped`. Termination is the theorem set in
`Spec/Termination.lean`; the loop itself is `partial` because it runs IO. -/
partial def loop (c : Ctx) (s : RunState) : IO RunState := do
  match s with
  | .built ctx st =>
    match frontier ctx.mods st with
    | [] =>
      let cert ← certificate c.target c.toolchain (c.aliases.normalize) c.files (statusList c st)
      stepL c s (.certificate cert) "certificate"
        (Json.mkObj [("built", toJson cert.built), ("decls", toJson cert.decls.length)])
    | m :: _ =>
      let (_, opens) ← diagnose c.target m (c.fileOf m) (propose c.aliases)
      let siteJson := opens.map fun o => Json.mkObj
        [("line", toJson o.site.diagnostic.line),
         ("class", toJson (toString (repr (classify o.site.diagnostic)))),
         ("decl", toJson o.site.decl),
         ("region", toJson (o.site.region.map fun r => toString (repr r))),
         ("candidates", toJson o.candidates.length)]
      loop c (← stepL c s (.diagnosed m opens) "diagnosed"
        (Json.mkObj [("module", toJson m), ("sites", toJson opens.length),
                     ("detail", Json.arr siteJson.toArray)]))
  | .mending _ _ mm =>
    match mm.next with
    | .finish =>
      let s' ← stepL c s .mended "mended" (toJson mm.module)
      match s' with
      | .built _ st' =>
        let (_, built) ← buildAll c.target c.targets c.order
        let merged := overlay st' built
        loop c (← stepL c s' (.build merged) "build" (toJson ((statusList c merged).map fun (n, x) => s!"{n}: {repr x}")))
      | other => pure other
    | .giveUp site =>
      loop c (← stepL c s (.mend .gaveUp) "gaveUp"
        (Json.mkObj [("module", toJson mm.module), ("line", toJson site.diagnostic.line),
                     ("text", toJson site.diagnostic.text)]))
    | .attempt cand =>
      let file := c.fileOf mm.module
      let saved ← applyEdit c.target file cand
      let (e, opens) ← diagnose c.target mm.module file (propose c.aliases)
      let s' ← stepL c s (.mend (.rebuilt e opens)) "rebuilt"
        (Json.mkObj [("rule", toJson cand.rule), ("errors", toJson e)])
      let acceptedNow := match s' with
        | .mending _ _ mm' => decide (mm'.accepted.length > mm.accepted.length)
        | _ => false
      if acceptedNow then
        discard <| git c.target #["add", file.toString]
        discard <| git c.target #["commit", "-q", "-m",
          s!"lean-mend: {cand.rule} in {mm.module}\n\nRule: {cand.rule}\nEntrenchment: {repr cand.entrenchment}"]
      else
        IO.FS.writeBinFile (c.target / file) saved
      loop c s'
  | other => pure other

/-- Run the `--prepare` command in a tree before its build, for example
`lake exe cache get` for a Mathlib project. It must succeed. -/
def prepareTree (tree : FilePath) : List String → IO Unit
  | [] => pure ()
  | cmd :: args => discard <| runOk tree cmd args.toArray

/-- `lean-mend run <target> --adopt [--targets <t,…>] [--prepare <cmd>] [--aliases-from <project>]…` -/
def runAdopt (target : FilePath) (targets : List String) (aliasesFrom : List FilePath)
    (prepare : List String := []) : IO RunState := do
  -- Absolute paths: git and lake run with the target as their working
  -- directory, so a relative path would resolve one level too deep.
  let target ← IO.FS.realPath target
  let aliasesFrom ← aliasesFrom.mapM IO.FS.realPath
  let status ← git target #["status", "--porcelain", "--untracked-files=no"]
  unless status.isEmpty do throw <| IO.userError s!"{target} has uncommitted changes"
  IO.FS.createDirAll (target / ".lean-mend")
  let ledger := target / ".lean-mend" / "ledger.jsonl"
  IO.FS.writeFile ledger ""
  -- The bumped tree at HEAD: graph and build (this also builds the dependencies).
  let toolchain := (← IO.FS.readFile (target / "lean-toolchain")).trimAscii.toString
  let files ← moduleGraph target
  let order0 ← match topoOrder (files.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{repr r}"
  prepareTree target prepare
  let (order, built) ← buildAll target targets order0
  -- The alias map: the dependencies at HEAD, and every --aliases-from project.
  let names := order.map (·.name)
  let external := (order.flatMap (·.imports)).filter (!names.contains ·) |>.eraseDups
  let mut pairs ← deprecated target external
  for p in aliasesFrom do
    pairs := pairs ++ (← deprecated p (← projectModules p))
  let raw : AliasMap := ⟨pairs.eraseDups⟩
  let resolved ← match raw.resolve with
    | some a => pure a
    | none => throw <| IO.userError "alias cycle"
  -- The baseline: HEAD~1 in a detached worktree.
  let base := target / ".lean-mend" / "base"
  if ← base.pathExists then discard <| git target #["worktree", "remove", "--force", base.toString]
  discard <| git target #["worktree", "add", "-q", "--detach", base.toString, "HEAD~1"]
  let baseFiles ← moduleGraph base
  let baseOrder0 ← match topoOrder (baseFiles.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{repr r}"
  prepareTree base prepare
  let (_, baseBuilt) ← buildAll base targets baseOrder0
  let baseToolchain := (← IO.FS.readFile (base / "lean-toolchain")).trimAscii.toString
  let baseCert ← certificate base baseToolchain resolved.normalize baseFiles baseBuilt
  let baseFailing := baseBuilt.filterMap fun (n, s) => if s == .built then none else some n
  let c : Ctx := { target, toolchain, files, order, targets, aliases := resolved, ledger }
  -- The machine, in its own order.
  let s ← stepL c (.idle target.toString) (.baseline baseCert baseFailing) "baseline"
    (Json.mkObj [("decls", toJson baseCert.decls.length), ("failing", toJson baseFailing)])
  let s ← stepL c s (.bumped (order) raw) "bumped"
    (Json.mkObj [("aliases", toJson (resolved.pairs.map fun (a, b) => s!"{a} → {b}"))])
  let s ← stepL c s (.build (overlay (fun _ => .blocked) built)) "build"
    (toJson (built.map fun (n, x) => s!"{n}: {repr x}"))
  discard <| git target #["switch", "-q", "-c", "lean-mend/mend"]
  let final ← loop c s
  discard <| git target #["worktree", "remove", "--force", base.toString]
  pure final

end LeanMend.Shell
