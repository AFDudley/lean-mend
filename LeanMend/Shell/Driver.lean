import LeanMend.Core.Ops
import LeanMend.Shell.Target
import LeanMend.Shell.Session

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

A wave is every current frontier module (`docs/parallel.md` § Level 2,
P8-P13): the driver mends every member at the same time, each in its own
attempt worktree (`planWaveModule`, `planModule`). Each member's plan is
computed in its own worktree, with no ledger write and no mend-branch commit;
the driver then replays every member's plan against the shared `RunState`
and the ledger, one member at a time in the wave's own canonical (module
topological) order (`replayDiagnosed`, `replayRounds`), so the ledger and the
commits come out exactly as a one-module-at-a-time run would write them, no
matter which member's worktree finished first (P10-P12). Only the driver
ever edits the main checkout or runs `git commit` there, so it is the only
writer of the mend branch (P11).

By default (`--speculate 1`), an attempt runs in the module's own wave
worktree, one candidate at a time; a rejected candidate is reverted by
restoring the file's previous bytes. `--speculate <n>` attempts the next `n`
head candidates at the same time, each in its own nested worktree
(`docs/parallel.md` P14-P16, `speculateRounds`); the plan keeps the last
accepted candidate until the Core picks a winner, in rule order.
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
  /-- Ratified and proposed rules, from `--rules` (the lean-mend source). -/
  rules : List Rule
  /-- `--annotate-binders`: apply the type-narrowing statement edit
  (decision D11). Off by default: the edit is reported as a warning. -/
  annotate : Bool
  /-- `--follow-definition-changes` (decision D12). -/
  follow : Bool
  /-- `--speculate <n>` (`docs/parallel.md` P14-P16): the width of the
  speculative window at the head site. `1` (the default) attempts one
  candidate at a time, in the target checkout, as before. -/
  speculate : Nat := 1
  /-- Rules accepted in a declaration body earlier in this run. -/
  followed : IO.Ref (List String)
  /-- Statement sites already warned about (decision D12). -/
  warned : IO.Ref (List String)
  /-- Declarations whose statement this run changed (decision D12). -/
  followedDecls : IO.Ref (List String)
  ledger : FilePath
  /-- The commit where `lean-mend/mend` starts. -/
  start : String

def Ctx.fileOf (c : Ctx) (module : String) : FilePath :=
  ((c.files.find? (·.1.name == module)).map (·.2)).getD module

/-- Append one ledger line (concept D1): the observation and the next state. -/
def appendLedger (ledger : FilePath) (obs : String) (detail : Json) (next : RunState) :
    IO Unit := do
  let h ← IO.FS.Handle.mk ledger .append
  h.putStrLn <| Json.compress <| Json.mkObj
    [("obs", toJson obs), ("detail", detail), ("state", toJson next.tag)]

/-- Append a warning line to the ledger: it changes no state. -/
def appendWarning (ledger : FilePath) (text : String) : IO Unit := do
  let h ← IO.FS.Handle.mk ledger .append
  h.putStrLn <| Json.compress <| Json.mkObj [("obs", toJson "warning"), ("detail", toJson text)]

/-- The warning lines of a ledger, in order. -/
def ledgerWarnings (ledger : FilePath) : IO (List String) := do
  let lines := ((← IO.FS.readFile ledger).splitOn "\n").filter (· ≠ "")
  pure <| lines.filterMap fun l => do
    let j ← (Json.parse l).toOption
    guard ((j.getObjValAs? String "obs").toOption == some "warning")
    (j.getObjValAs? String "detail").toOption

def record (c : Ctx) (obs : String) (detail : Json) (next : RunState) : IO Unit :=
  appendLedger c.ledger obs detail next

def stepL (c : Ctx) (s : RunState) (obs : RunObs) (name : String) (detail : Json := Json.null) :
    IO RunState := do
  let next := s.step obs
  record c name detail next
  pure next

/-- The one member this (sequential) driver is working: it starts one
`Mending` per wave and finishes it before diagnosing the next frontier
module, so the fleet in `.mending` always holds exactly one member here
(`docs/parallel.md` § S3a; the parallel fleet is `LeanMend.Shell.Driver`'s
future, S3b). -/
def soleMending (f : Fleet) : IO Mending :=
  match f.mendings with
  | [mm] => pure mm
  | _ => throw <| IO.userError "lean-mend: the fleet does not hold exactly one Mending"

/-- Statuses as the machine sees them: the shell's build result, except that a
module the machine closed as `residual` stays `residual`. -/
def overlay (machine : Statuses) (built : List (String × ModStatus)) : Statuses :=
  fun n => if machine n == .residual then .residual else (built.lookup n).getD .built

def statusList (c : Ctx) (st : Statuses) : List (String × ModStatus) :=
  c.order.map fun m => (m.name, st m.name)

def git (target : FilePath) (args : Array String) : IO String := runOk target "git" args

/-- Symlink `dir`'s copy of every Lake package's `.lake` build directory
(the main checkout's own, and every nested path dependency's) to the same
package's `.lake` under `c.target` (`docs/parallel.md` P18). `dir` is a
`git worktree add` checkout: it holds every package's tracked source, never
a package's untracked build output, and `lake env lean --json` (`diagnose`,
`attemptOne`) only ever reads that output through `LEAN_PATH` — `buildAll`,
the only writer, always runs against `c.target` directly, never inside a
wave or speculative attempt worktree, so every worktree can safely share
one copy. -/
def symlinkLakeDirs (c : Ctx) (dir : FilePath) : IO Unit := do
  let link (srcRoot dstRoot : FilePath) : IO Unit := do
    let src := srcRoot / ".lake"
    if ← src.pathExists then
      IO.FS.createDirAll dstRoot
      discard <| runOk dir "ln" #["-s", src.toString, (dstRoot / ".lake").toString]
  link c.target dir
  for p in ← nestedPackageRoots c.target do
    link (c.target / p) (dir / p)

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

/-- Decision D12 without the flag: write one warning per statement site that
the run would change to follow a definition change. -/
def warnFollow (c : Ctx) (m : String) (done : List String) (nodesAt : List (Site × List Node)) :
    IO Unit := do
  if c.follow then return
  for (site, ns) in nodesAt do
    for t in followCandidates (c.rules.filter (done.contains ·.name)) ns site do
      let key := s!"{site.decl.getD "?"}:{site.diagnostic.line}"
      unless (← c.warned.get).contains key do
        c.warned.modify (key :: ·)
        appendWarning c.ledger s!"{m}:{site.diagnostic.line} {site.decl.getD "?"}: \
          would change the statement `{t.replacement.take 60}…` to follow a definition change; \
          rerun with --follow-definition-changes"

/-- Apply `cand` under `target` and rebuild `mm.module`, as `Mending.step`
expects (`docs/parallel.md` P14): `target` is one module's own wave worktree
(`planModule`), or one nested worktree of a speculative attempt
(`speculateRounds`). Returns the file's previous bytes (unused once the
caller only ever discards or replays this worktree, never the main
checkout directly), the `rebuilt` observation, the `done` rule-name list
`commitAccepted` and `warnFollow` need, and the nodes at the attempted site.

`followedSnapshot`, when given, replaces a live read of `c.followed`: a
wave's modules plan at the same time (`docs/parallel.md` P8), so each one
reads the single snapshot taken before the wave started, never another
module's mid-wave accept — `c.followed` only gains that accept once the
driver replays it, after the whole wave is planned. `none` (the sequential
`--speculate 1` single-module path, outside a wave) reads `c.followed` live,
as before. -/
def attemptOne (c : Ctx) (target : FilePath) (mm : Mending) (file : FilePath) (cand : Candidate)
    (session : ProbeSession) (followedSnapshot : Option (List String) := none) :
    IO (ByteArray × MendObs × List String × List (Site × List Node)) := do
  let saved ← applyEdit target file cand
  let followed ← match followedSnapshot with
    | some d => pure d
    | none => c.followed.get
  let done := followed ++
    (match cand.target with | .body _ => [(cand.rule.splitOn ": ").head!] | _ => [])
  let (e, _, lints, opens0, nodesAt) ← diagnose session target mm.module file c.aliases c.rules c.annotate c.follow
    (if c.follow then done else [])
  let opens := opens0.filter fun o => !mm.residue.any (·.sameAs o.site)
  let editEnd := cand.start + cand.replacement.utf8ByteSize
  let spans := if cand.changed.isEmpty then [(cand.start, editEnd)] else cand.changed
  let inEdit := lints.filter fun (o, _) => spans.any fun (a, b) => a ≤ o && o < b
  let lint := inEdit.length
  let unused := inEdit.filterMap (·.2)
  pure (saved, .rebuilt e lint unused opens, done, nodesAt)

/-- The ledger detail of a `rebuilt` observation, for the step named `"rebuilt"`. -/
def rebuiltDetail (rule : String) : MendObs → Json
  | .rebuilt e lint unused _ =>
    Json.mkObj [("rule", toJson rule), ("errors", toJson e), ("lint", toJson lint),
                ("unused", toJson unused)]
  | _ => Json.null

/-- The side effects of a candidate the Core accepted: the decision-D11/D12
bookkeeping and the mend-branch commit. Only the driver writes the mend
branch (`docs/parallel.md` P11). -/
def commitAccepted (c : Ctx) (m : String) (file : FilePath) (cand : Candidate)
    (done : List String) (nodesAt : List (Site × List Node)) : IO Unit := do
  if let .typeAnnotation d := cand.target then
    appendWarning c.ledger s!"narrowed binders of type {d} in {m}: {cand.rule}"
  if let .followStatement d := cand.target then
    c.followedDecls.modify (d :: ·)
    appendWarning c.ledger s!"changed the statement of {d} in {m} to follow a definition change: {cand.rule}"
  if let .body _ := cand.target then
    c.followed.modify fun xs => (cand.rule.splitOn ": ").head! :: xs
  warnFollow c m done nodesAt
  discard <| git c.target #["add", file.toString]
  discard <| git c.target #["commit", "-q", "-m",
    s!"lean-mend: {cand.rule} in {m}\n\nRule: {cand.rule}\nEntrenchment: {repr cand.entrenchment}"]

/-- One round of `planModule`: either one attempted candidate (an
`attempt`, `.rebuilt`/`.unparsable`) or a give-up (`.gaveUp`, no candidate).
Computed inside a module's own wave worktree with no ledger write and no
mend-branch commit, so the same round replays identically regardless of
when, relative to another module's own rounds, it was computed
(`docs/parallel.md` P8, P11, P12). `accepted` is `Mending.step`'s own
verdict on this round, decided once while planning; `replayRounds` only
replays it, never re-decides it. -/
structure WaveRound where
  obs : MendObs
  name : String
  detail : Json
  cand : Option Candidate
  done : List String
  nodesAt : List (Site × List Node)
  accepted : Bool
  startedAt : Nat
  finishedAt : Nat
  worktree : FilePath
  /-- Extra ledger lines `replayRounds` writes before this round's own
  (`.mend`) transition, each as `(name, detail)` against the round's own
  `s` (no state change) — the speculative-candidate records
  (`speculateAttempt`, `speculateResult`) a `--speculate n > 1` attempt
  still writes, so `tests/speculate.sh` sees the same ledger shape it saw
  before S3b. -/
  extra : List (String × Json) := []
  /-- This round's 1-based position in its speculative candidate list, for
  `speculateResult`'s `acceptedIndex`. `none` outside a speculative round. -/
  specIndex : Option Nat := none

/-- Speculate across the head site's candidates of `mm`, inside `dir` (one
module's own wave worktree, or the lone module's worktree outside a wave):
the next `c.speculate` candidates, each in its own nested worktree, attempted
at the same time (`docs/parallel.md` P14). Feeds `Mending.step` their
verdicts in rule order (P15): a reject for every one that failed, then an
accept at the first that passed. Stops at the first accept, or at the first
verdict that does not plainly reject (a cleaning, or a refusal): the
remaining precomputed results no longer match the Core's state, so the round
list ends there and `planModule` resumes at the new head. Every candidate
after the one it stops at is discarded without being recorded anywhere
(P16): this function writes no ledger line and makes no mend-branch commit,
by construction — only `replayRounds` ever does either, later, from the
rounds this returns. -/
partial def speculateRounds (c : Ctx) (dir : FilePath) (followedSnapshot : List String)
    (mm : Mending) (file : FilePath) : IO (List WaveRound × Mending) := do
  let cands := mm.speculate c.speculate
  let base := ((← git dir #["rev-parse", "HEAD"]).splitOn "\n").head!
  let dirs := (List.range cands.length).map fun i => dir / ".lean-mend" / s!"attempt-{i + 1}"
  -- `git worktree add` writes the shared `.git/worktrees` directory, so the
  -- driver serializes it; the rebuild each starts is what runs at the same
  -- time.
  for d in dirs do
    discard <| git dir #["worktree", "add", "-q", "--detach", d.toString, base]
    symlinkLakeDirs c d
  let tasks ← (dirs.zip cands).mapM fun (d, cd) =>
    IO.asTask
      (do
        let startedAt ← IO.monoMsNow
        -- One probe process for this one nested attempt (`docs/parallel.md`
        -- C1): each nested worktree is its own process's cwd, and the
        -- candidates run at the same time, so they cannot share one. It stops
        -- on every exit path, so no probe process outlives the attempt.
        let session ← probeServeStart d
        let (_, obs, done, nodesAt) ← (do
          try attemptOne c d mm file cd session followedSnapshot
          finally probeServeStop session)
        let finishedAt ← IO.monoMsNow
        pure (cd, d, obs, done, nodesAt, startedAt, finishedAt))
      (prio := .dedicated)
  let rec consume :
      List (Task (Except IO.Error
        (Candidate × FilePath × MendObs × List String × List (Site × List Node) × Nat × Nat))) →
      Nat → Mending → IO (List WaveRound × Mending)
    | [], _, mmc => pure ([], mmc)
    | t :: rest, i, mmc => do
      let (cd, d, obs, done, nodesAt, startedAt, finishedAt) ← IO.ofExcept t.get
      match mmc.step obs with
      | .error r => throw <| IO.userError s!"lean-mend: {mmc.module}: {repr r}"
      | .ok mmc' =>
        let accepted := mmc'.accepted.length > mmc.accepted.length
        let round : WaveRound :=
          { obs, name := "rebuilt", detail := rebuiltDetail cd.rule obs, cand := some cd,
            done, nodesAt, accepted, startedAt, finishedAt, worktree := d, specIndex := some (i + 1)
            extra := [("speculateAttempt",
              Json.mkObj [("index", toJson (i + 1)), ("worktree", toJson d.toString),
                          ("rule", toJson cd.rule), ("startedAt", toJson startedAt),
                          ("finishedAt", toJson finishedAt)])] }
        if accepted then pure ([round], mmc')
        else if (mmc'.sites.head?.map (·.candidates.length)) ==
            (mmc.sites.head?.map fun o => o.candidates.length - 1) then
          let (rest', mmFinal) ← consume rest (i + 1) mmc'
          pure (round :: rest', mmFinal)
        else pure ([round], mmc')
  let (rounds, mmFinal) ← consume tasks 0 mm
  for d in dirs do
    discard <| git dir #["worktree", "remove", "--force", d.toString]
  -- `speculateResult`'s `acceptedIndex`: the accepted candidate's rule-order
  -- position, or `none` if every speculated candidate was rejected (or the
  -- batch stopped early on a cleaning). Attached to the last round, so
  -- `replayRounds` writes it right after that round's own ledger line, as
  -- the sequential run did.
  let acceptedIndex := if rounds.getLast?.map (·.accepted) == some true then
    rounds.getLast?.bind (·.specIndex) else none
  let resultExtra : String × Json :=
    ("speculateResult", Json.mkObj [("module", toJson mm.module), ("acceptedIndex", toJson acceptedIndex)])
  let rounds := match rounds.reverse with
    | [] => []
    | last :: earlierRev => ({ last with extra := last.extra ++ [resultExtra] } :: earlierRev).reverse
  pure (rounds, mmFinal)

/-- Plan one module's whole wave-mend session inside `dir`, from `mm`'s
current state to `Mending.next = .finish`: the sequence of `WaveRound`s a
one-module-at-a-time run would see, decided by `Mending.step` exactly as it
decides for a live run, but with no ledger write and no mend-branch commit
(`docs/parallel.md` P8). `planWaveModule` runs this as a background task, one
per wave member, so every member's build happens at the same time; the
driver only ever reads the returned rounds back, later, in the wave's own
canonical order (`replayRounds`). -/
partial def planModule (c : Ctx) (dir : FilePath) (followedSnapshot : List String) (mm : Mending)
    (session : ProbeSession) : IO (List WaveRound) := do
  let file := c.fileOf mm.module
  match mm.next with
  | .finish => pure []
  | .giveUp site =>
    match mm.step .gaveUp with
    | .error r => throw <| IO.userError s!"lean-mend: {mm.module}: {repr r}"
    | .ok mm' =>
      let now ← IO.monoMsNow
      let round : WaveRound :=
        { obs := .gaveUp, name := "gaveUp",
          detail := Json.mkObj [("module", toJson mm.module), ("line", toJson site.diagnostic.line),
                                 ("text", toJson site.diagnostic.text)],
          cand := none, done := [], nodesAt := [], accepted := false,
          startedAt := now, finishedAt := now, worktree := dir }
      pure (round :: (← planModule c dir followedSnapshot mm' session))
  | .attempt cand =>
    if c.speculate ≤ 1 then
      -- `dir` holds one attempt at a time, as `Mending.step` expects
      -- (concept D3: nested worktrees are level 3 only). A rejected edit is
      -- reverted before the next attempt reuses this same worktree. Every
      -- attempt on this module, in this worktree, shares `session`
      -- (`docs/parallel.md` C1).
      let startedAt ← IO.monoMsNow
      let (saved, obs, done, nodesAt) ← attemptOne c dir mm file cand session followedSnapshot
      let finishedAt ← IO.monoMsNow
      match mm.step obs with
      | .error r => throw <| IO.userError s!"lean-mend: {mm.module}: {repr r}"
      | .ok mm' =>
        let accepted := mm'.accepted.length > mm.accepted.length
        unless accepted do
          IO.FS.writeBinFile (dir / file) saved
        let round : WaveRound :=
          { obs, name := "rebuilt", detail := rebuiltDetail cand.rule obs, cand := some cand,
            done, nodesAt, accepted, startedAt, finishedAt, worktree := dir }
        pure (round :: (← planModule c dir followedSnapshot mm' session))
    else
      let (rounds, mm') ← speculateRounds c dir followedSnapshot mm file
      pure (rounds ++ (← planModule c dir followedSnapshot mm' session))

/-- One wave member's plan: the module's initial diagnose (for the
`.diagnosed` replay) and its full round sequence (for the `.mend` replays),
with the worktree `planWaveModule` computed it in. -/
structure WavePlan where
  module : String
  decls : Nat
  opens : List Open
  nodesAt0 : List (Site × List Node)
  rounds : List WaveRound
  dir : FilePath

/-- Diagnose `m` inside its own wave worktree `dir`, build the initial
`Mending` the same way `RunState.step` would for a live `.diagnosed`
observation (reusing it on the real `ctx`/`st`, since `m` is already known
to be a member of `frontier ctx.mods st`), then plan the whole session
(`planModule`). This is the one background task per wave member
(`docs/parallel.md` P8); the driver starts one per member, then replays each
member's plan in the wave's own canonical order (`loop`). -/
def planWaveModule (c : Ctx) (ctx : Context) (st : Statuses) (followedSnapshot : List String)
    (dir : FilePath) (m : String) : IO WavePlan := do
  -- One probe process for the whole of `m`'s wave-mend session in `dir`
  -- (`docs/parallel.md` C1): the initial diagnose below and every attempt
  -- `planModule` makes share it. It stops once this plan is computed, or when
  -- the plan fails, so no probe process outlives the run.
  let session ← probeServeStart dir
  try
    let (_, decls, _, opens, nodesAt0) ← diagnose session dir m (c.fileOf m) c.aliases c.rules c.annotate c.follow
      (if c.follow then followedSnapshot else [])
    let mm0 ← match RunState.step (.built ctx st) (.diagnosed m decls opens) with
      | .mending _ _ f => soleMending f
      | .halted r => throw <| IO.userError s!"lean-mend: {m}: {repr r}"
      | _ => throw <| IO.userError s!"lean-mend: {m}: diagnosed did not enter mending"
    let rounds ← planModule c dir followedSnapshot mm0 session
    pure { module := m, decls, opens, nodesAt0, rounds, dir }
  finally probeServeStop session

/-- Replay `plan`'s initial diagnose against the shared ledger and
`RunState` (`docs/parallel.md` P12): the same warnings, in the same order,
that the `.built` branch of `loop` wrote for one module before S3b, now
written once per wave member, in the wave's own canonical order. Also
records the one probe process `planWaveModule` started for this module
(`docs/parallel.md` C1): the background computation phase writes no ledger
line of its own, so the fact is recorded here, in canonical order, like
every other observation this replay makes. -/
def replayDiagnosed (c : Ctx) (s : RunState) (plan : WavePlan) : IO RunState := do
  let done ← c.followed.get
  record c "probeStart" (Json.mkObj [("module", toJson plan.module)]) s
  warnFollow c plan.module done plan.nodesAt0
  -- Decision D11: without --annotate-binders, report the type narrowing the
  -- run would apply, and leave the site as residue.
  unless c.annotate do
    for o in plan.opens do
      for t in typeCandidates o.site do
        appendWarning c.ledger s!"{plan.module}:{o.site.diagnostic.line} {o.site.decl.getD "?"}: \
          would narrow `{o.site.text}` to `{t.replacement}`; rerun with --annotate-binders"
  let siteJson := plan.opens.map fun o => Json.mkObj
    [("line", toJson o.site.diagnostic.line),
     ("class", toJson (toString (repr (classify o.site.diagnostic)))),
     ("decl", toJson o.site.decl),
     ("region", toJson (o.site.region.map fun r => toString (repr r))),
     ("candidates", toJson o.candidates.length)]
  stepL c s (.diagnosed plan.module plan.decls plan.opens) "diagnosed"
    (Json.mkObj [("module", toJson plan.module), ("sites", toJson plan.opens.length),
                 ("detail", Json.arr siteJson.toArray)])

/-- Replay `plan`'s rounds against the shared ledger, `RunState` and the main
checkout, in the module's own round order (`docs/parallel.md` P10, P12): an
accepted round's candidate is applied to the main checkout and committed
there — the only place any candidate from this wave is ever applied or
committed (P11) — then the module is closed with `.mended`. -/
def replayRounds (c : Ctx) (s : RunState) (plan : WavePlan) : IO RunState := do
  let mut s := s
  for r in plan.rounds do
    record c "waveAttempt"
      (Json.mkObj [("module", toJson plan.module), ("worktree", toJson r.worktree.toString),
                   ("rule", toJson (r.cand.map (·.rule))),
                   ("startedAt", toJson r.startedAt), ("finishedAt", toJson r.finishedAt)]) s
    for (name, detail) in r.extra do
      record c name detail s
    s ← stepL c s (.mend plan.module r.obs) r.name r.detail
    if r.accepted then
      let some cand := r.cand
        | throw <| IO.userError "lean-mend: an accepted wave round names no candidate"
      let file := c.fileOf plan.module
      discard <| applyEdit c.target file cand
      commitAccepted c plan.module file cand r.done r.nodesAt
  stepL c s (.mended plan.module) "mended" (toJson plan.module)

/-- The level-1 loop, after `bumped`. Termination is the theorem set in
`Spec/Termination.lean`; the loop itself is `partial` because it runs IO.

A wave is every current frontier module (`docs/parallel.md` § Level 2): the
driver mends every member at the same time, each in its own attempt
worktree (P8), then replays every member's plan, one member at a time, in
the wave's own canonical (module topological) order — `frontier` already
returns the members in `ctx.mods`'s topological order (`Core.Run.frontier`)
— so the ledger and the mend-branch commits come out exactly as a
one-module-at-a-time run would write them (P10, P12), whichever member's
worktree finished first. -/
partial def loop (c : Ctx) (s : RunState) : IO RunState := do
  match s with
  | .built ctx st =>
    match frontier ctx.mods st with
    | [] =>
      let cert0 ← certificate c.target c.toolchain (c.aliases.normalizeWith (Rule.prefixPairs c.rules)) c.files (statusList c st)
      let cert := { cert0 with followed := (← c.followedDecls.get).eraseDups }
      let next ← stepL c s (.certificate cert) "certificate"
        (Json.mkObj [("built", toJson cert.built), ("decls", toJson cert.decls.length)])
      for (d, why) in typeChanges ctx.aliases ctx.base cert do
        appendWarning c.ledger s!"type {d.name} in {d.module} {why} (decision D11)"
      let (residue, fs) := match next with
        | .awaiting _ _ r _ fs => (r, fs)
        | .done _ _ r _ => (r, [])
        | _ => ([], [])
      let cards := fs.zipIdx.filterMap fun (f, i) =>
        f.reason.card.map fun k => ({ id := s!"c-{i + 1}", kind := k,
                                      subject := ctx.aliases.rename f.decl.name } : Card)
      writeCards c.target
        { target := c.target.toString, start := c.start, base := ctx.base, after := cert,
          mods := ctx.mods, aliases := ctx.aliases, residue, cards } fs c.fileOf
      pure next
    | wave =>
      let followedSnapshot ← c.followed.get
      let base := ((← git c.target #["rev-parse", "HEAD"]).splitOn "\n").head!
      let dirs := (List.range wave.length).map fun i => c.target / ".lean-mend" / s!"wave-{i + 1}"
      for dir in dirs do
        discard <| git c.target #["worktree", "add", "-q", "--detach", dir.toString, base]
        symlinkLakeDirs c dir
      record c "waveStart"
        (Json.mkObj [("modules", toJson wave), ("worktrees", toJson (dirs.map FilePath.toString))]) s
      let tasks ← (dirs.zip wave).mapM fun (dir, m) =>
        IO.asTask (planWaveModule c ctx st followedSnapshot dir m) (prio := .dedicated)
      let mut plans : List WavePlan := []
      for t in tasks do
        plans := plans ++ [← IO.ofExcept t.get]
      for dir in dirs do
        discard <| git c.target #["worktree", "remove", "--force", dir.toString]
      record c "waveCleanup" (Json.mkObj [("removed", toJson (dirs.map FilePath.toString))]) s
      let mut s' := s
      for plan in plans do
        s' ← replayDiagnosed c s' plan
      for plan in plans do
        s' ← replayRounds c s' plan
      match s' with
      | .built _ st' =>
        let (_, built) ← buildAll c.target c.targets c.order
        let merged := overlay st' built
        loop c (← stepL c s' (.build merged) "build" (toJson ((statusList c merged).map fun (n, x) => s!"{n}: {repr x}")))
      | other => pure other
  | other => pure other

/-- Run the `--prepare` command in a tree before any Lake command there, for
example `lake exe cache get` when the target's own dependencies need fetching,
or a copy of a saved `.lake`. The first Lake command (the probe's `lake env`)
resolves the manifest and clones every package into a missing `.lake`, so a
prepare that runs after it finds the tree already populated. It must succeed. -/
def prepareTree (tree : FilePath) : List String → IO Unit
  | [] => pure ()
  | cmd :: args => discard <| runOk tree cmd args.toArray

/-- `lean-mend run <target> --adopt [--targets <t,…>] [--prepare <cmd>] [--aliases-from <project>]…` -/
def runAdopt (target : FilePath) (targets : List String) (aliasesFrom : List FilePath)
    (prepare : List String := []) (rules : List Rule := []) (annotate : Bool := false)
    (follow : Bool := false) (speculate : Nat := 1) : IO RunState := do
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
  prepareTree target prepare
  let files ← moduleGraph target
  let order0 ← match topoOrder (files.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{repr r}"
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
  -- A crashed run can leave the worktree registered with its directory gone.
  discard <| git target #["worktree", "prune"]
  if ← base.pathExists then discard <| git target #["worktree", "remove", "--force", base.toString]
  discard <| git target #["worktree", "add", "-q", "--detach", base.toString, "HEAD~1"]
  prepareTree base prepare
  let baseFiles ← moduleGraph base
  let baseOrder0 ← match topoOrder (baseFiles.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{repr r}"
  let (_, baseBuilt) ← buildAll base targets baseOrder0
  let baseToolchain := (← IO.FS.readFile (base / "lean-toolchain")).trimAscii.toString
  let baseCert ← certificate base baseToolchain (resolved.normalizeWith (Rule.prefixPairs rules)) baseFiles baseBuilt
  let baseFailing := baseBuilt.filterMap fun (n, s) => if s == .built then none else some n
  -- A namespace move also renames declarations the target itself declares
  -- under the moved prefix (EVMLean: `def Batteries.RBMap.partition`). Give
  -- each one an exact alias, so `compare` and the cards find it after the move.
  let moved := baseCert.decls.filterMap fun d =>
    (Rule.prefixPairs rules).findSome? fun (a, b) => (swapPrefix a b d.name).map (d.name, ·)
  let raw : AliasMap := ⟨(raw.pairs ++ moved).eraseDups⟩
  let resolved ← match raw.resolve with
    | some a => pure a
    | none => throw <| IO.userError "alias cycle"
  let followed ← IO.mkRef ([] : List String)
  let warned ← IO.mkRef ([] : List String)
  let followedDecls ← IO.mkRef ([] : List String)
  let c : Ctx := { target, toolchain, files, order, targets, aliases := resolved, rules, annotate,
                   follow, speculate, followed, warned, followedDecls, ledger,
                   start := "" }
  -- The machine, in its own order.
  let s ← stepL c (.idle target.toString) (.baseline baseCert baseFailing) "baseline"
    (Json.mkObj [("decls", toJson baseCert.decls.length), ("failing", toJson baseFailing)])
  let s ← stepL c s (.bumped (order) raw) "bumped"
    (Json.mkObj [("aliases", toJson (resolved.pairs.map fun (a, b) => s!"{a} → {b}"))])
  let s ← stepL c s (.build (overlay (fun _ => .blocked) built)) "build"
    (toJson (built.map fun (n, x) => s!"{n}: {repr x}"))
  discard <| git target #["switch", "-q", "-c", "lean-mend/mend"]
  let start := ((← git target #["rev-parse", "HEAD"]).splitOn "\n").head!
  let final ← loop { c with start } s
  discard <| git target #["worktree", "remove", "--force", base.toString]
  pure final

/-- The judgments recorded in a ledger, in order. -/
def ledgerJudgments (ledger : FilePath) : IO (List Judgment) := do
  let lines := ((← IO.FS.readFile ledger).splitOn "\n").filter (· ≠ "")
  lines.filterMapM fun l => do
    let some j := (Json.parse l).toOption | return none
    unless (j.getObjValAs? String "obs").toOption == some "judgment" do return none
    let some d := (j.getObjVal? "detail").toOption | return none
    let field (k : String) := ((d.getObjValAs? String k).toOption).getD ""
    let kind ← match cardKindOf (field "kind") with
      | .ok k => pure k
      | .error e => throw <| IO.userError s!"ledger judgment: {e}"
    return some { card := field "card", kind, subject := field "subject",
                  answer := if field "answer" == "accept" then .accept else .reject,
                  author := field "author", at_ := field "at" }

/-- `lean-mend judge <target> <card> accept|reject --by <name>`: record a
person's judgment on a card and step the machine (`RunState.step`, `judgment`). -/
def judge (target : FilePath) (cardId : String) (answer : Answer) (author : String) :
    IO RunState := do
  let target ← IO.FS.realPath target
  let ledger := target / ".lean-mend" / "ledger.jsonl"
  let s ← parseOrThrow "session" ((Json.parse (← IO.FS.readFile (sessionPath target))) >>= sessionOf)
  let some card := s.cards.find? (·.id == cardId)
    | throw <| IO.userError s!"no card {cardId} in this session"
  let prior ← ledgerJudgments ledger
  let state := RunState.close s.context s.after s.residue prior
  let at_ := ((← runOk target "date" #["-u", "+%FT%TZ"]).splitOn "\n").head!
  let j : Judgment := { card := card.id, kind := card.kind, subject := card.subject,
                        answer, author, at_ }
  let next := state.step (.judgment j)
  appendLedger ledger "judgment"
    (Json.mkObj [("card", toJson j.card), ("kind", toJson (cardKindName j.kind)),
                 ("subject", toJson j.subject),
                 ("answer", toJson (if answer == .accept then "accept" else "reject")),
                 ("author", toJson author), ("at", toJson at_)]) next
  pure next

/-- The cards of a session that no judgment has answered. -/
def openCards (target : FilePath) : IO (List Card) := do
  let target ← IO.FS.realPath target
  let s ← parseOrThrow "session" ((Json.parse (← IO.FS.readFile (sessionPath target))) >>= sessionOf)
  let js ← ledgerJudgments (target / ".lean-mend" / "ledger.jsonl")
  pure (s.cards.filter fun c => !js.any (·.card == c.id))

end LeanMend.Shell
