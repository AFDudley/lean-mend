import Std.Data.HashMap
import LeanMend.Shell.Memory
import LeanMend.Core.Ops
import LeanMend.Core.Sched
import LeanMend.Shell.Target
import LeanMend.Shell.Session
import LeanMend.Shell.CompEq

/-!
# The driver

The composition root (concept A3): the only module that knows both the machine
(`RunState.step`, `Mending.next`) and the adapters (`Shell.Target`). It makes
each observation, appends it to the ledger, and calls the pure transition.
See `docs/machine.md` and `docs/architecture.md`.

`lean-mend run <target> --adopt` handles a target that another tool already
bumped: the baseline is the parent commit (`HEAD~1`), checked out in a
detached worktree under `<target>/.lean-mend/base`. The run keeps that
worktree, and a later run at the same parent commit reuses it, so Lake
rebuilds only what changed (`baseTree`). The baseline certificate is stored
under a key of all its inputs (`baseCertificate`, law LM3). The bumped tree
and the baseline build at the same time (`buildBoth`). The mend branch is
`lean-mend/mend`, created at `HEAD`. Each accepted patch is one commit on it.

The modules mend in dataflow order (`docs/parallel.md` § Level 2, P8, P10-P13,
P21-P23, `dataflow`). A module starts as soon as every module it imports
builds with its mended text (`Core.Run.ready`), each in its own attempt
worktree (`planSession`), and it does not wait for an unrelated module. When
a mend ends, the driver writes the mended file into the main checkout and
builds that one module (`settle`), so the modules that import it can start.
That step makes no commit and writes no ledger line. The driver replays each
module's plan against the shared `RunState`, the ledger and the mend branch
in the canonical order: the head of `ready` over the machine's own statuses,
which is the module topological order (`advance`, `replayDiagnosed`,
`replayRounds`). So the ledger and the commits come out as a
one-module-at-a-time run writes them, whichever worktree finished first
(P10, P12). Only the driver edits the main checkout or runs `git commit`
there, so it is the only writer of the mend branch (P11).

By default (`--speculate 4`, `defaultSpeculate`), an attempt takes the
next four head candidates at the same time (`docs/parallel.md` P14-P16,
P25, `speculateRounds`): the first on the module's own probe, each other one
in its own nested worktree when the probe bound admits it; the plan keeps
the last accepted candidate until the Core picks a winner, in rule order.
`--speculate 1` attempts one candidate at a time in the module's own
worktree; a rejected candidate is reverted by restoring the file's previous
bytes.

One limit bounds the private memory of the driver and every process it
starts (`docs/parallel.md` P17, P24, `Ctx.gate`): a module starts its probe
only when the measured tree plus the probe budget fits, and it waits with no
probe and no thread until running work ends (`launch`).
-/

namespace LeanMend.Shell

open System (FilePath)
open Lean (Json toJson)

/-- A typed stop of the run (fail fast). `lean-mend run` prints it and exits
3. -/
inductive RunStop where
  /-- A probe passed its memory cap (`docs/parallel.md` P24). -/
  | capExceeded (x : CapExceeded)
  /-- The certificate has no row for a declaration that it selects
  (`docs/verification.md` § The certificate). -/
  | declUnread (x : DeclUnread)

def RunStop.message : RunStop → String
  | .capExceeded x => x.message
  | .declUnread x => x.message

/-- The ledger note of the stop, and the fields that `lean-mend run` prints
after its `state`. -/
def RunStop.note : RunStop → String × List (String × Json)
  | .capExceeded x => ("capExceeded",
    [("module", toJson x.module), ("capKiB", toJson x.cap.val), ("peakKiB", toJson x.peak.val)])
  | .declUnread x => ("declUnread",
    [("module", toJson x.module), ("decl", toJson x.decl), ("reason", toJson x.reason)])

/-- The default width of the speculative window at the head site
(`docs/parallel.md` P25). -/
def defaultSpeculate : Nat := 4

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
  /-- `--speculate <n>` (`docs/parallel.md` P14-P16, P25): the width of the
  speculative window at the head site. `1` attempts one candidate at a time,
  in the module's own worktree; the default (`defaultSpeculate`) takes the
  next four. -/
  speculate : Nat := defaultSpeculate
  /-- The memory gate of the run (`docs/parallel.md` P24): every probe
  process starts only on an admission of the gate. -/
  gate : Gate
  /-- The hard cap of each probe process (`docs/parallel.md` P24):
  `probeCap`, or `--probe-cap <MiB>`. -/
  probeCap : KiB
  /-- The typed stop of the run, set when a probe passes its cap or the
  certificate has no row for a declaration. -/
  stop : IO.Ref (Option RunStop)
  /-- Rules accepted in a declaration body earlier in this run. -/
  followed : IO.Ref (List String)
  /-- Statement sites already warned about (decision D12). -/
  warned : IO.Ref (List String)
  /-- Declarations whose statement this run changed (decision D12). -/
  followedDecls : IO.Ref (List String)
  ledger : FilePath
  /-- The commit where `lean-mend/mend` starts. -/
  start : String
  /-- The base worktree, at the baseline commit and the old toolchain, with
  its build. The cards' evidence reads it at `certificate`
  (`docs/verification.md` § What a card explains). -/
  base : FilePath
  /-- Every module of the base worktree with its file. -/
  baseFiles : List (Module × FilePath)

def Ctx.fileOf (c : Ctx) (module : String) : FilePath :=
  ((c.files.find? (·.1.name == module)).map (·.2)).getD module

/-- Append one ledger line (concept D1): the observation and the next state. -/
def appendLedger (ledger : FilePath) (obs : String) (detail : Json) (next : RunState) :
    IO Unit := do
  let h ← IO.FS.Handle.mk ledger .append
  h.putStrLn <| Json.compress <| Json.mkObj
    [("obs", toJson obs), ("detail", detail), ("state", toJson next.tag)]

/-- Append a line to the ledger that changes no state: a warning, or the
run-start `probeBound` line (`docs/parallel.md` P24). -/
def appendNote (ledger : FilePath) (obs : String) (detail : Json) : IO Unit := do
  let h ← IO.FS.Handle.mk ledger .append
  h.putStrLn <| Json.compress <| Json.mkObj [("obs", toJson obs), ("detail", detail)]

/-- Append a warning line to the ledger: it changes no state. -/
def appendWarning (ledger : FilePath) (text : String) : IO Unit :=
  appendNote ledger "warning" (toJson text)

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

/-- The one member of the fleet: the driver replays one module at a time, in
the canonical order (`docs/parallel.md` P12), so the fleet in `.mending`
always holds exactly one member here. -/
def soleMending (f : Fleet) : IO Mending :=
  match f.mendings with
  | [mm] => pure mm
  | _ => throw <| IO.userError "lean-mend: the fleet does not hold exactly one Mending"

/-- Statuses as the machine sees them: the shell's build result, except that a
module the machine closed as `residual` stays `residual`. The build result
is a hash map, so one lookup does not scan the whole module list (about
10,000 modules on EquiVM). -/
def overlay (machine : Statuses) (built : List (String × ModStatus)) : Statuses :=
  let m : Std.HashMap String ModStatus := Std.HashMap.ofList built
  fun n => if machine n == .residual then .residual else m.getD n .built

def statusList (c : Ctx) (st : Statuses) : List (String × ModStatus) :=
  c.order.map fun m => (m.name, st m.name)

def git (target : FilePath) (args : Array String) : IO String := runOk target "git" args

/-- Symlink `dir`'s copy of every Lake package's `.lake` build directory
(the main checkout's own, and every nested path dependency's) to the same
package's `.lake` under `c.target` (`docs/parallel.md` P18). `dir` is a
`git worktree add` checkout: it holds every package's tracked source, never
a package's untracked build output, and every Lean process that an attempt
starts with `lake env` (`diagnose`, `attemptOne`) only ever reads that
output through `LEAN_PATH` — `buildAll`,
the only writer, always runs against `c.target` directly, never inside a
module or speculative attempt worktree, so every worktree can safely share
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

/-- One decision-D12 warning without the flag: the statement site that the
run would change to follow a definition change, if the rule `rule` was
accepted in a body. `key` names the site, so each site gets one warning. -/
structure FollowWarning where
  rule : String
  key : String
  text : String

/-- The decision-D12 warnings of one diagnose, for every rule. The driver
computes them where the syntax nodes are, and a plan keeps only these lines,
not the nodes: the nodes of every open site of every round held most of the
driver's memory on EquiVM run 7 (`docs/parallel.md` P24). -/
def followWarnings (c : Ctx) (m : String) (nodesAt : List (Site × List Node)) : List FollowWarning :=
  if c.follow then [] else
  nodesAt.flatMap fun (site, ns) => c.rules.flatMap fun r =>
    (followCandidates [r] ns site).map fun t =>
      { rule := r.name, key := s!"{site.decl.getD "?"}:{site.diagnostic.line}",
        text := s!"{m}:{site.diagnostic.line} {site.decl.getD "?"}: \
          would change the statement `{t.replacement.take 60}…` to follow a definition change; \
          rerun with --follow-definition-changes" }

/-- Decision D12 without the flag: write one warning per statement site that
the run would change to follow a definition change, for the rules in
`done`. -/
def warnFollow (c : Ctx) (done : List String) (ws : List FollowWarning) : IO Unit := do
  for w in ws do
    if done.contains w.rule then
      unless (← c.warned.get).contains w.key do
        c.warned.modify (w.key :: ·)
        appendWarning c.ledger w.text

/-- The rule name that an accepted body edit adds to the followed rules
(decision D12), or `none` for an edit outside a body. -/
def bodyRule (cand : Candidate) : Option String :=
  match cand.target with
  | .body _ => some (cand.rule.splitOn ": ").head!
  | _ => none

/-- Apply `cand` under `target` and rebuild `mm.module`, as `Mending.step`
expects (`docs/parallel.md` P14): `target` is one module's own worktree
(`planModule`), or one nested worktree of a speculative attempt
(`speculateRounds`). Returns the file's previous bytes, for a revert, the
`rebuilt` observation, the `done` rule-name list `commitAccepted` needs, and
the decision-D12 warnings of the new text (`followWarnings`).

`followed` is the module's followed-rule snapshot (`docs/parallel.md` P22):
the body rules accepted in the modules it imports. Modules mend at the same
time, so an attempt never reads the live `c.followed`, which gains a rule
only when the driver replays it. -/
def attemptOne (c : Ctx) (target : FilePath) (mm : Mending) (file : FilePath) (cand : Candidate)
    (session : ProbeSession) (followed : List String) :
    IO (ByteArray × MendObs × List String × List FollowWarning) := do
  let saved ← applyEdit target file cand
  let done := followed ++ (bodyRule cand).toList
  let (e, _, lints, opens0, nodesAt) ← diagnose session target mm.module file c.aliases c.rules c.annotate c.follow
    (if c.follow then done else [])
  let opens := opens0.filter fun o => !mm.residue.any (·.sameAs o.site)
  let editEnd := cand.start + cand.replacement.utf8ByteSize
  let spans := if cand.changed.isEmpty then [(cand.start, editEnd)] else cand.changed
  let inEdit := lints.filter fun (o, _) => spans.any fun (a, b) => a ≤ o && o < b
  let lint := inEdit.length
  let unused := inEdit.filterMap (·.2)
  pure (saved, .rebuilt e lint unused opens, done, followWarnings c mm.module nodesAt)

/-- The ledger detail of a `rebuilt` observation, for the step named `"rebuilt"`. -/
def rebuiltDetail (rule : String) : MendObs → Json
  | .rebuilt e lint unused _ =>
    Json.mkObj [("rule", toJson rule), ("errors", toJson e), ("lint", toJson lint),
                ("unused", toJson unused)]
  | _ => Json.null

/-- The side effects of a candidate the Core accepted: the decision-D11/D12
bookkeeping and the mend-branch commit of `text`, the module file's text
with this candidate applied. Only the driver writes the mend branch
(`docs/parallel.md` P11). The commit goes through the git index, not the
working tree (P23): the main checkout already holds the module's final text,
which a running `lake build` of a module that imports it reads. `mode` is the
file's git mode. -/
def commitAccepted (c : Ctx) (m : String) (file : FilePath) (mode : String) (text : ByteArray)
    (cand : Candidate) (done : List String) (follows : List FollowWarning) : IO Unit := do
  if let .typeAnnotation d := cand.target then
    appendWarning c.ledger s!"narrowed binders of type {d} in {m}: {cand.rule}"
  if let .followStatement d := cand.target then
    c.followedDecls.modify (d :: ·)
    appendWarning c.ledger s!"changed the statement of {d} in {m} to follow a definition change: {cand.rule}"
  if let some r := bodyRule cand then
    c.followed.modify (r :: ·)
  warnFollow c done follows
  let blob := c.target / ".lean-mend" / "commit.blob"
  IO.FS.writeBinFile blob text
  let sha := (← git c.target #["hash-object", "-w", "--path", file.toString, blob.toString]).trimAscii.toString
  discard <| git c.target #["update-index", "--cacheinfo", s!"{mode},{sha},{file}"]
  discard <| git c.target #["commit", "-q", "-m",
    s!"lean-mend: {cand.rule} in {m}\n\nRule: {cand.rule}\nEntrenchment: {repr cand.entrenchment}"]

/-- One round of `planModule`: either one attempted candidate (an
`attempt`, `.rebuilt`/`.unparsable`) or a give-up (`.gaveUp`, no candidate).
Computed inside a module's own worktree with no ledger write and no
mend-branch commit, so the same round replays identically regardless of
when, relative to another module's own rounds, it was computed
(`docs/parallel.md` P8, P11, P12). `accepted` is `Mending.step`'s own
verdict on this round, decided once while planning; `replayRounds` only
replays it, never re-decides it. -/
structure ModuleRound where
  obs : MendObs
  name : String
  detail : Json
  cand : Option Candidate
  done : List String
  follows : List FollowWarning
  accepted : Bool
  startedAt : Nat
  finishedAt : Nat
  worktree : FilePath
  /-- Extra ledger lines `replayRounds` writes before this round's own
  (`.mend`) transition, each as `(name, detail)` against the round's own
  `s` (no state change): the speculative-candidate records
  (`speculateAttempt`, `speculateResult`) of a `--speculate n > 1` attempt,
  which `tests/speculate.sh` reads. -/
  extra : List (String × Json) := []
  /-- This round's 1-based position in its speculative candidate list, for
  `speculateResult`'s `acceptedIndex`. `none` outside a speculative round. -/
  specIndex : Option Nat := none

/-- One probe process, for the ledger: the gate's admission, the times the
process started and stopped, and its peak resident size at its last reply
(`docs/parallel.md` P24). -/
structure ProbeRecord where
  admission : Admission
  startedAt : Nat
  stoppedAt : Nat
  peak : KiB

/-- Run `f` on a new probe process for `module` in `dir`, on the admission
`adm` of the gate, under the hard cap `c.probeCap`. The process stops, and
then the gate releases its place, on every exit path, so the gate counts
every live probe. The gate knows the session from its start, so the stop of
the run ends it (`Gate.stop`). When Lean stopped the probe at its cap, the
run stops with `CapExceeded` (`c.stop`): the error names the module, the cap
and the peak. -/
def onProbe {α} (c : Ctx) (adm : Admission) (module : String) (dir : FilePath)
    (f : ProbeSession → IO α) : IO (α × ProbeRecord) := do
  try
    let startedAt ← IO.monoMsNow
    -- The typed stop (`docs/parallel.md` P24), at the cap text on the
    -- probe's stderr: record `CapExceeded`, then stop the run at once. The
    -- gate ends every other live probe (`Gate.stop`), also a nested probe of
    -- a speculative round that `f` waits for, so the stop does not wait for
    -- `f` to end.
    let capStop (peak : KiB) : IO Unit := do
      c.stop.modify (·.orElse fun _ => some (.capExceeded { module, cap := c.probeCap, peak }))
      c.gate.stop
    let session ← probeServeStart dir c.probeCap capStop
    c.gate.started adm.ticket session
    let capped : IO α := do
      try f session
      catch e => do
        unless ← session.overCap.get do throw e
        let stop : CapExceeded := { module, cap := session.cap, peak := ← session.peak.get }
        throw <| IO.userError stop.message
    let a ← try capped finally probeServeStop session
    pure (a, { admission := adm, startedAt, stoppedAt := ← IO.monoMsNow, peak := ← session.peak.get })
  finally c.gate.release adm.ticket

/-- The `probeStart` ledger line of a probe: the module, the worktree, the
time, and what the gate charged and measured at its admission. -/
def ProbeRecord.startLine (r : ProbeRecord) (module : String) (dir : FilePath) : String × Json :=
  ("probeStart", Json.mkObj ([("module", toJson module), ("worktree", toJson dir.toString),
    ("at", toJson r.startedAt)] ++ r.admission.fields))

/-- The `probeStop` ledger line of a probe, with its peak resident size. -/
def ProbeRecord.stopLine (r : ProbeRecord) (module : String) (dir : FilePath) : String × Json :=
  ("probeStop", Json.mkObj [("module", toJson module), ("worktree", toJson dir.toString),
    ("at", toJson r.stoppedAt), ("peakKiB", toJson r.peak.val)])

/-- One attempted candidate of a speculative round. `probe` holds the start
and stop times of the candidate's own probe process, or `none` when the
candidate ran on the module's own probe. -/
structure SpecResult where
  cand : Candidate
  dir : FilePath
  obs : MendObs
  done : List String
  follows : List FollowWarning
  startedAt : Nat
  finishedAt : Nat
  probe : Option ProbeRecord

/-- One candidate of a speculative round (`Core.Sched.roundPlacement`): on
the module's own probe, attempted when `consume` reaches it, or on a nested
probe in the worktree `dir`, already running. -/
inductive SpecRun where
  | own (cand : Candidate)
  | nested (dir : FilePath) (task : Task (Except IO.Error SpecResult))

/-- Speculate across the head site's candidates of `mm`, inside `dir` (one
module's own worktree): the next `c.speculate` candidates, attempted at the
same time (`docs/parallel.md` P14). Feeds `Mending.step` their verdicts in
rule order (P15): a reject for every one that failed, then an accept at the
first that passed. Stops at the first accept, or at the first verdict that
does not plainly reject (a cleaning, or a refusal): the remaining
precomputed results no longer match the Core's state, so the round list ends
there and `planModule` resumes at the new head. The result of every
candidate after the one it stops at is discarded without being recorded
anywhere (P16): this function writes no ledger line and makes no mend-branch
commit, by construction — only `replayRounds` ever does either, later, from
the rounds this returns.

The memory limit (`docs/parallel.md` P24): the round already holds the
admission of `session`, its module's own probe. It asks the gate for
`roundExtra` other probes with no wait (`Gate.tryAcquire`), and
`roundPlacement` places the candidates. The first candidate, and each
candidate that got no admission, runs on `session` in `dir`, in rule order.
Each other candidate runs on its own probe in its own nested worktree. So
the round never waits for memory while it holds a probe, and it progresses
for every limit.

Each nested worktree starts from `dir`'s commit, so it holds the mended text
of every module that `dir`'s module imports (`addWorktree`). It then gets
`dir`'s current text of the module file, which holds the edits the plan
accepted before this round. A candidate on `session` is reverted to that
text after its attempt. An accepted candidate is applied to `dir` at the end,
so `planModule`'s next round and the plan's final text hold it. The round
waits for every nested probe to stop before it removes the nested
worktrees, so no probe process outlives its worktree. It waits also when a
candidate's attempt fails, and then throws the first error. -/
partial def speculateRounds (c : Ctx) (dir : FilePath) (followed : List String)
    (mm : Mending) (file : FilePath) (session : ProbeSession) : IO (List ModuleRound × Mending) := do
  let cands := mm.speculate c.speculate
  let base := ((← git dir #["rev-parse", "HEAD"]).splitOn "\n").head!
  let current ← IO.FS.readBinFile (dir / file)
  let rec grab : Nat → IO (List Admission)
    | 0 => pure []
    | n + 1 => do
      let some a ← c.gate.tryAcquire | pure []
      pure (a :: (← grab n))
  let admissions ← grab (roundExtra cands.length)
  let placed := (cands.zip (roundPlacement cands.length admissions.length)).zipIdx
  -- `git worktree add` writes the shared `.git/worktrees` directory, so the
  -- driver serializes it; the rebuild each starts is what runs at the same
  -- time.
  let runs ← placed.mapM fun ((cd, p), i) => do
    match p, admissions[i - 1]? with
    | .nested, some adm =>
      let d := dir / ".lean-mend" / s!"attempt-{i + 1}"
      discard <| git dir #["worktree", "add", "-q", "--detach", d.toString, base]
      symlinkLakeDirs c d
      IO.FS.writeBinFile (d / file) current
      -- One probe process for this one nested attempt (`docs/parallel.md`
      -- C1), on an admission that `grab` got: each nested worktree is its
      -- own process's cwd, and the candidates run at the same time, so they
      -- cannot share one.
      let t ← IO.asTask (prio := .dedicated) do
        let ((obs, done, follows, startedAt, finishedAt), probe) ←
          onProbe c adm mm.module d fun s => do
            let startedAt ← IO.monoMsNow
            let (_, obs, done, follows) ← attemptOne c d mm file cd s followed
            pure (obs, done, follows, startedAt, ← IO.monoMsNow)
        pure { cand := cd, dir := d, obs, done, follows, startedAt, finishedAt,
               probe := some probe : SpecResult }
      pure (SpecRun.nested d t)
    | _, _ => pure (SpecRun.own cd)
  let result : SpecRun → IO SpecResult
    | .nested _ t => do IO.ofExcept (← IO.wait t)
    | .own cd => do
      let startedAt ← IO.monoMsNow
      let (saved, obs, done, follows) ← attemptOne c dir mm file cd session followed
      IO.FS.writeBinFile (dir / file) saved
      pure { cand := cd, dir, obs, done, follows, startedAt, finishedAt := ← IO.monoMsNow,
             probe := none }
  let rec consume : List SpecRun → Nat → Mending → IO (List ModuleRound × Mending)
    | [], _, mmc => pure ([], mmc)
    | r :: rest, i, mmc => do
      let { cand := cd, dir := d, obs, done, follows, startedAt, finishedAt, .. } ← result r
      match mmc.step obs with
      | .error r => throw <| IO.userError s!"lean-mend: {mmc.module}: {repr r}"
      | .ok mmc' =>
        let accepted := mmc'.accepted.length > mmc.accepted.length
        let round : ModuleRound :=
          { obs, name := "rebuilt", detail := rebuiltDetail cd.rule obs, cand := some cd,
            done, follows, accepted, startedAt, finishedAt, worktree := d, specIndex := some (i + 1)
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
  let consumed ← (consume runs 0 mm).toBaseIO
  -- Every nested probe, also of a discarded candidate: wait for its stop,
  -- then remove its worktree. After an error too, so no probe process
  -- outlives its worktree.
  let ended ← (runs.filterMap fun | .nested d t => some (d, t) | .own _ => none).mapM fun (d, t) => do
    let r ← IO.wait t
    discard <| git dir #["worktree", "remove", "--force", d.toString]
    pure r
  let (rounds, mmFinal) ← IO.ofExcept consumed
  -- The start and stop of each nested probe.
  let mut probes : List (String × Json) := []
  for r in ended do
    let res ← IO.ofExcept r
    if let some pr := res.probe then
      probes := probes ++ [pr.startLine mm.module res.dir, pr.stopLine mm.module res.dir]
  if let some last := rounds.getLast? then
    if last.accepted then
      let some cd := last.cand
        | throw <| IO.userError "lean-mend: an accepted speculative round names no candidate"
      discard <| applyEdit dir file cd
  -- `speculateResult`'s `acceptedIndex`: the accepted candidate's rule-order
  -- position, or `none` if every speculated candidate was rejected (or the
  -- batch stopped early on a cleaning). Attached to the last round, so
  -- `replayRounds` writes it right after that round's own ledger line, as
  -- the sequential run did. The nested probes' lines come before it.
  let acceptedIndex := if rounds.getLast?.map (·.accepted) == some true then
    rounds.getLast?.bind (·.specIndex) else none
  let resultExtra : String × Json :=
    ("speculateResult", Json.mkObj [("module", toJson mm.module), ("acceptedIndex", toJson acceptedIndex)])
  let rounds := match rounds.reverse with
    | [] => []
    | last :: earlierRev =>
      ({ last with extra := last.extra ++ probes ++ [resultExtra] } :: earlierRev).reverse
  pure (rounds, mmFinal)

/-- Plan one module's whole mend session inside `dir`, from `mm`'s current
state to `Mending.next = .finish`: the sequence of `ModuleRound`s a
one-module-at-a-time run would see, decided by `Mending.step` exactly as it
decides for a live run, but with no ledger write and no mend-branch commit
(`docs/parallel.md` P8), and the final `Mending`. `planSession` runs this
as a background task, one per module, so independent modules build at the
same time; the driver only reads the returned rounds back, later, in the
canonical order (`replayRounds`). -/
partial def planModule (c : Ctx) (dir : FilePath) (followed : List String) (mm : Mending)
    (session : ProbeSession) : IO (List ModuleRound × Mending) := do
  let file := c.fileOf mm.module
  let continue_ (rounds : List ModuleRound) (mm' : Mending) : IO (List ModuleRound × Mending) := do
    let (rest, mmFinal) ← planModule c dir followed mm' session
    pure (rounds ++ rest, mmFinal)
  match mm.next with
  | .finish => pure ([], mm)
  | .giveUp site =>
    match mm.step .gaveUp with
    | .error r => throw <| IO.userError s!"lean-mend: {mm.module}: {repr r}"
    | .ok mm' =>
      let now ← IO.monoMsNow
      let round : ModuleRound :=
        { obs := .gaveUp, name := "gaveUp",
          detail := Json.mkObj [("module", toJson mm.module), ("line", toJson site.diagnostic.line),
                                 ("text", toJson site.diagnostic.text)],
          cand := none, done := [], follows := [], accepted := false,
          startedAt := now, finishedAt := now, worktree := dir }
      continue_ [round] mm'
  | .attempt cand =>
    if c.speculate ≤ 1 then
      -- `dir` holds one attempt at a time, as `Mending.step` expects
      -- (concept D3: nested worktrees are level 3 only). A rejected edit is
      -- reverted before the next attempt reuses this same worktree. Every
      -- attempt on this module, in this worktree, shares `session`
      -- (`docs/parallel.md` C1).
      let startedAt ← IO.monoMsNow
      let (saved, obs, done, follows) ← attemptOne c dir mm file cand session followed
      let finishedAt ← IO.monoMsNow
      match mm.step obs with
      | .error r => throw <| IO.userError s!"lean-mend: {mm.module}: {repr r}"
      | .ok mm' =>
        let accepted := mm'.accepted.length > mm.accepted.length
        unless accepted do
          IO.FS.writeBinFile (dir / file) saved
        let round : ModuleRound :=
          { obs, name := "rebuilt", detail := rebuiltDetail cand.rule obs, cand := some cand,
            done, follows, accepted, startedAt, finishedAt, worktree := dir }
        continue_ [round] mm'
    else
      let (rounds, mm') ← speculateRounds c dir followed mm file session
      continue_ rounds mm'

/-- One module's plan: the module's initial diagnose (for the `.diagnosed`
replay), its full round sequence (for the `.mend` replays), the worktree
`planSession` computed it in, and the module file's text at the start and at
the end of the mend. A plan waits for its replay until every module before
it in the canonical order replays, so it keeps no syntax node: only the
decision-D12 warnings that the nodes give (`followWarnings`). -/
structure ModulePlan where
  module : String
  decls : Nat
  opens : List Open
  /-- The decision-D12 warnings of the initial diagnose. -/
  follows0 : List FollowWarning
  rounds : List ModuleRound
  dir : FilePath
  startText : ByteArray
  text : ByteArray
  /-- The mend ended with one or more residue sites, so the module closes
  `residual` and does not build. -/
  residue : Bool
  /-- The module's own probe process (`docs/parallel.md` P24), for the
  ledger's `probeStart` and `probeStop`. -/
  probe : ProbeRecord

/-- The body rules this plan accepted, in round order: the part of the
followed-rule snapshot that every module importing this one receives
(`docs/parallel.md` P22). -/
def ModulePlan.bodyRules (p : ModulePlan) : List String :=
  p.rounds.filterMap fun r => if r.accepted then r.cand.bind bodyRule else none

/-- Diagnose `m` inside its own worktree `dir`, build the initial `Mending`
the same way `RunState.step` would for a live `.diagnosed` observation (on
the live statuses `st`, where `m` is a frontier module), then plan the whole
session (`planModule`). This is the one background task per module
(`docs/parallel.md` P8); the driver replays its plan in the canonical order
(`advance`). `adm` is the gate's admission of the module's probe (`launch`). -/
def planSession (c : Ctx) (ctx : Context) (st : Statuses) (followed : List String)
    (dir : FilePath) (m : String) (adm : Admission) : IO ModulePlan := do
  let file := c.fileOf m
  let startText ← IO.FS.readBinFile (dir / file)
  -- One probe process for the whole of `m`'s mend session in `dir`
  -- (`docs/parallel.md` C1): the initial diagnose below and every attempt
  -- `planModule` makes share it. It stops once this plan is computed, or when
  -- the plan fails, and then the gate frees its place (P24).
  let (plan, probe) ← onProbe c adm m dir fun session => do
    let (_, decls, _, opens, nodesAt0) ← diagnose session dir m file c.aliases c.rules c.annotate c.follow
      (if c.follow then followed else [])
    let mm0 ← match RunState.step (.built ctx st) (.diagnosed m decls opens) with
      | .mending _ _ f => soleMending f
      | .halted r => throw <| IO.userError s!"lean-mend: {m}: {repr r}"
      | _ => throw <| IO.userError s!"lean-mend: {m}: diagnosed did not enter mending"
    let (rounds, mmFinal) ← planModule c dir followed mm0 session
    pure (decls, opens, followWarnings c m nodesAt0, rounds, !mmFinal.residue.isEmpty)
  let (decls, opens, follows0, rounds, residue) := plan
  pure { module := m, decls, opens, follows0, rounds, dir, startText,
         text := ← IO.FS.readBinFile (dir / file), residue, probe }

/-- Replay `plan`'s initial diagnose against the shared ledger and
`RunState` (`docs/parallel.md` P12): the warnings of decisions D11 and D12,
then the `diagnosed` observation. Also records the start of the one probe
process `planSession` started for this module (`docs/parallel.md` C1, P24;
`replayRounds` records its stop): the background computation writes no
ledger line of its own, so the fact is recorded here, in canonical order,
like every other observation this replay makes. -/
def replayDiagnosed (c : Ctx) (s : RunState) (plan : ModulePlan) : IO RunState := do
  let done ← c.followed.get
  let (name, detail) := plan.probe.startLine plan.module plan.dir
  record c name detail s
  warnFollow c done plan.follows0
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

/-- Replay `plan`'s rounds against the shared ledger, `RunState` and the mend
branch, in the module's own round order (`docs/parallel.md` P10, P12): each
accepted round's candidate is applied to the module's text in memory, from
the text the plan started with, and committed through the git index (P11,
P23); then the module is closed with `.mended`. The candidates must give
the text that the mend ended with, which `settle` already wrote into the
main checkout. -/
def replayRounds (c : Ctx) (s : RunState) (plan : ModulePlan) : IO RunState := do
  let file := c.fileOf plan.module
  let mode := ((← git c.target #["ls-files", "--stage", "--", file.toString]).splitOn " ").head!
  let mut s := s
  let mut text := plan.startText
  for r in plan.rounds do
    record c "moduleAttempt"
      (Json.mkObj [("module", toJson plan.module), ("worktree", toJson r.worktree.toString),
                   ("rule", toJson (r.cand.map (·.rule))),
                   ("startedAt", toJson r.startedAt), ("finishedAt", toJson r.finishedAt)]) s
    for (name, detail) in r.extra do
      record c name detail s
    s ← stepL c s (.mend plan.module r.obs) r.name r.detail
    if r.accepted then
      let some cand := r.cand
        | throw <| IO.userError "lean-mend: an accepted round names no candidate"
      text := spliceEdit text cand
      commitAccepted c plan.module file mode text cand r.done r.follows
  unless text.data == plan.text.data do
    throw <| IO.userError s!"lean-mend: {plan.module}: the accepted candidates do not give the text the mend ended with"
  let (name, detail) := plan.probe.stopLine plan.module plan.dir
  record c name detail s
  stepL c s (.mended plan.module) "mended" (toJson plan.module)

/-- Accept a Behavior finding at once, with no card, when its body change
lies wholly inside a proof at both toolchains (`docs/decisions.md` D16;
`docs/static-diff.md` § 6, decision S6; `docs/verification.md` § What a card
explains, the proof-term rule). The judgment is `lean-mend`'s own: it goes
into the ledger and the session exactly as a person's judgment does, so the
evidence stays on record, but the finding never becomes a card. Any other
Behavior finding is untouched; `certify` gives it a card, and the card states
why the check failed (`behaviorText`, `ch.outside`). -/
def autoAcceptProofOnly (c : Ctx) (aliases : AliasMap) (evidence : Evidence) (next : RunState) :
    IO RunState := do
  let beh : List Finding := match next with
    | .awaiting _ _ _ _ fs => fs.filter (·.reason == .definitionChanged)
    | _ => []
  let mut st := next
  for f in beh do
    let subj := aliases.rename f.decl.name
    let proofOnly := match evidence.bodies.lookup subj with
      | some (b, a) => (bodyChange b a).proofOnly
      | none => false
    if proofOnly then
      let at_ := ((← runOk c.target "date" #["-u", "+%FT%TZ"]).splitOn "\n").head!
      let j : Judgment := { card := "auto:proofOnly", kind := .behavior, subject := subj,
                            answer := .accept, author := "lean-mend: proof-only check", at_ }
      st ← stepL c st (.judgment j) "judgment"
        (Json.mkObj [("card", toJson j.card), ("kind", toJson (cardKindName j.kind)),
                     ("subject", toJson j.subject), ("answer", toJson "accept"),
                     ("author", toJson j.author), ("at", toJson at_)])
  pure st

/-- Certify computational equality (`docs/static-diff.md` § 4) of every
Behavior finding decision D16's proof-only check (`autoAcceptProofOnly`)
left open: `LeanMend.Shell.certifyBehaviors`, one `terms` call per side for
the whole round, not one per declaration (the cost rule,
`.scratch/static-diff-review.md`). A certified-equal finding auto-accepts
exactly as the proof-only check does, with its trust points in the ledger
note (decision D16's own pattern, extended by decision S6: a card is
issued only after a recorded, failed certification attempt). A finding
`certifyEqual` cannot certify stays open; `certify` still gives it a card,
and every finding examined — certified or not — gets one `compEq` ledger
note, so the card-writer can read the verdict back and name the first
differing subterm (`LeanMend.Shell.Session.compEqText`). -/
def autoAcceptCompEq (c : Ctx) (aliases : AliasMap) (baseTree afterTree : Tree)
    (next : RunState) : IO RunState := do
  let allFindings : List Finding := match next with
    | .awaiting _ _ _ _ fs => fs
    | _ => []
  let beh := allFindings.filter (·.reason == .definitionChanged)
  if beh.isEmpty then return next
  let results ← certifyBehaviors (Names.ofAliases aliases) baseTree afterTree allFindings beh
  let mut st := next
  for (subj, r) in results do
    let trustPointsJson (tps : List TrustPoint) : Json :=
      Json.arr (tps.toArray.map fun (t : TrustPoint) =>
        Json.mkObj [("name", toJson t.name), ("kind", toJson t.kind)])
    let detail := match r with
      | .certified tps => Json.mkObj
          [("subject", toJson subj), ("result", toJson "certified"),
           ("trustPoints", trustPointsJson tps)]
      | .differsAt cst reason => Json.mkObj
          [("subject", toJson subj), ("result", toJson "differsAt"),
           ("constant", toJson cst), ("reason", toJson reason)]
    appendNote c.ledger "compEq" detail
    if let .certified tps := r then
      let at_ := ((← runOk c.target "date" #["-u", "+%FT%TZ"]).splitOn "\n").head!
      let j : Judgment := { card := "auto:compEq", kind := .behavior, subject := subj,
                            answer := .accept, author := "lean-mend: computational equality check", at_ }
      st ← stepL c st (.judgment j) "judgment"
        (Json.mkObj [("card", toJson j.card), ("kind", toJson (cardKindName j.kind)),
                     ("subject", toJson j.subject), ("answer", toJson "accept"),
                     ("author", toJson j.author), ("at", toJson at_),
                     ("trustPoints", trustPointsJson tps)])
  pure st


/-! ## Level 3: axiom repair (`docs/machine.md` § Level 3) -/

/-- The target's own package name, from `lake-manifest.json`'s own `name`
field (`docs/machine.md` § The site of an axiom finding: `rootPackage` is
the target's own package). `"the target"` when the tree has no manifest. -/
def rootPackageOf (target : FilePath) : IO String := do
  pure (((← manifestRevs target).map (·.1)).getD "the target")

/-- The `CauseTag` of a finding's cause (`docs/rules.md` § Axiom-finding
rules): `congrLemma` when the cause constant carries `@[congr]` in the
evidence of the toolchain that has the axiom, `matcher` when it is a
generated matcher (its last name component starts with `match_`) whose
`uses` hold `Nat.hasNotBit`, else `any`. -/
def causeTagOf (baseIdx afterIdx : Std.HashMap String Const) (cause : AxiomCause) : CauseTag :=
  let idx := if cause.change == .added then afterIdx else baseIdx
  let n := cause.cause.here.name
  match idx[n]? with
  | some c =>
    if c.congr then .congrLemma
    else if ((n.splitOn ".").getLast!.startsWith "match_") && c.uses.contains "Nat.hasNotBit" then .matcher
    else .any
  | none => .any

/-- `(id, decl, explanations)` triples for `groupFindingSites`, over every
open Violation finding's cause (`explainViolation`), the same computation
`Shell.Session.writeCards` makes for the cards, with a synthetic id (not a
card id: `sites3` is gathered before any card exists). -/
def violationCards (ctx : Context) (cert : Certificate) (evidence : Evidence) (fs : List Finding) :
    List (String × String × List AxiomExplanation) :=
  let names := Names.ofAliases ctx.aliases
  fs.zipIdx.filterMap fun (f, i) =>
    let subject := ctx.aliases.rename f.decl.name
    (cert.decls.find? (·.name == subject)).map fun a =>
      (s!"f-{i}", subject, explainViolation names evidence.base evidence.after f.decl a)

/-- The Level 3 candidate groups for `fs`'s open Violation findings
(`docs/machine.md` § Level 3): `groupFindingSites` over their causes,
excluding a site already in `ctx.exhaustedSites` (`docs/machine.md` §
Termination, Level 3), each with the candidates its matching rules give
(`findingCandidates`), from the declaration's own insertion point
(`declRegion`, D17-aware) and the syntax node `causeTactic` finds. -/
def buildSites3 (c : Ctx) (ctx : Context) (cert : Certificate) (evidence : Evidence)
    (fs : List Finding) : IO (List OpenFindingSite) := do
  let rootPackage ← rootPackageOf c.target
  let cards := violationCards ctx cert evidence fs
  let groups := (groupFindingSites rootPackage cards).filter
    fun g => !ctx.exhaustedSites.contains g.key.site.1
  let baseIdx := evidence.base.index
  let afterIdx := evidence.after.index
  groups.filterMapM fun g => do
    let (decl, module) := g.key.site
    let file := c.fileOf module
    match ← declRegion c.target file decl with
    | none => pure none
    | some region =>
      let declStart := region.mutualStart.getD region.range.1
      let tag := causeTagOf baseIdx afterIdx g.first
      let node ← causeTactic c.target file declStart g.first.cause.here.name
      let src ← IO.FS.readFile (c.target / file)
      let (bodyStart, bodyStop) := region.body
      let body := some (bodyStart, String.fromUTF8! (src.toUTF8.extract bodyStart bodyStop))
      pure (some { group := g, candidates := findingCandidates c.rules tag g declStart node body })

/-- The site declaration's own kind, from the baseline certificate
(`docs/machine.md` § A def, instance or abbrev site). -/
def siteKindOf (ctx : Context) (decl : String) : DeclKind :=
  ((ctx.base.decls.find? (·.name == decl)).map (·.kind)).getD .other

/-- Whether `cand`'s edit can only affect a proof, never what the
declaration computes (`docs/machine.md` § Acceptance): a `theorem`'s edit
always is (`kind.computes = false`); a `def`/`instance`/`abbrev` body edit
is, only when its changed bytes lie wholly inside a proof sub-term of the
rebuilt body (the same test `bodyChange` uses, decision D16); a
`beforeDecl` insertion (`setOptionBefore`, `heartbeats`) on a computing
declaration can change its compiled form, so it never is. -/
def attemptIsProofOnly (c : Ctx) (computes : Bool) (file : FilePath) (decl : String)
    (cand : Candidate) : IO Bool := do
  if !computes then return true
  let .body _ := cand.target | return false
  match ← declRegion c.target file decl with
  | none => pure false
  | some region =>
    let tree : Tree := { dir := c.target, toolchain := c.toolchain, files := c.files, commit := "",
                          probe := probe c.target, request := c.target / ".lean-mend" / "repair-proofs.json" }
    let ranges ← runProofs tree file [region.body]
    pure (inProof (ranges.headD []) (cand.start, cand.start + cand.replacement.utf8ByteSize))

/-- `lake build -v +m` in the main checkout: the status of the one module `m`
(`docs/parallel.md` P13, P21). `buildAll` stays the only writer of the build
output (P18). -/
def buildModule (c : Ctx) (m : String) : IO ModStatus := do
  let (_, st) ← buildAll c.target [s!"+{m}"] c.order
  match st.lookup m with
  | some s => pure s
  | none => throw <| IO.userError s!"lean-mend: lake build +{m} reports no job for {m}"

/-- Attempt `g`'s head candidate `cand` (`docs/machine.md` § Acceptance):
apply the edit to the site's module in the main checkout, rebuild that
module alone (S0b probe elaborate, a fast first check), and — only once
that is clean — `lake build` it (`buildModule`), so its `.olean` is fresh
for `moduleCertificate`'s `decls-batch`, which imports the module rather
than reading its source. A proof-only edit restores condition 1 by the
walk, substituting the rebuilt module's fresh axioms (decision D15); a
computation-changing edit instead rebuilds the modules of `g`'s own
members that are not the site's module — "the importers that use a
changed declaration". Reverts the file on anything but acceptance, and
returns the module's final bytes on acceptance, for the mend-branch
commit. The `Json` names the condition-1 method (`"walk"` or `"rebuild"`)
and, for `"rebuild"`, the importer modules it rebuilt, so the ledger
states which path condition 1 took. -/
def attemptRepair (c : Ctx) (ctx : Context) (evidence : Evidence) (g : FindingSiteGroup)
    (cand : Candidate) : IO (FindingObs × Option ByteArray × Json) := do
  let decl := g.key.site.1
  let module := g.key.site.2
  let file := c.fileOf module
  let norm := c.aliases.normalizeWith (Rule.prefixPairs c.rules)
  let saved ← applyEdit c.target file cand
  let revert : IO (FindingObs × Option ByteArray × Json) := do
    IO.FS.writeBinFile (c.target / file) saved
    pure (.rejected, none, Json.null)
  -- `buildAndCertify`: the fast probe-elaborate check (S0b), then, only if
  -- clean, a real `lake build` (so the module's `.olean` reflects the
  -- edit) and its certificate.
  let buildAndCertify (m : String) (f : FilePath) : IO (Option (List Decl)) := do
    let errs ← rebuildModule c.target c.probeCap m f
    if !errs.isEmpty then pure none else
    match ← buildModule c m with
    | .built =>
      match ← moduleCertificate c.target c.toolchain norm m f with
      | .error x =>
        c.stop.modify (·.orElse fun _ => some (.declUnread x))
        throw <| IO.userError x.message
      | .ok cert' => pure (some cert'.decls)
    | _ => pure none
  match ← buildAndCertify module file with
  | none => revert
  | some siteDecls =>
  -- `decl`'s own body text changed by design (that is the edit); a
  -- synthetic accepted judgment keeps `compare` from flagging that
  -- change as an unaccepted Behavior finding here. Condition 1's own
  -- axiom check (`restoredFor`, below) still holds the edit to account.
  let selfAccept : Judgment :=
    { card := "attemptRepair", kind := .behavior, subject := decl, answer := .accept,
      author := "lean-mend", at_ := "" }
  let siteFindings := compare ctx.aliases ctx.base
    { toolchain := ctx.base.toolchain, built := [module], decls := siteDecls } [selfAccept]
  if !siteFindings.isEmpty then revert else
  let restoredFor (d : String) (newAxioms : List String) : Bool :=
    newAxioms == (((ctx.base.decls.find? (·.name == d)).map (·.axioms)).getD [])
  let computes := (siteKindOf ctx decl).computes
  let proofOnly ← attemptIsProofOnly c computes file decl cand
  if proofOnly then
    let override : Std.HashMap String (List String) :=
      siteDecls.foldl (init := {}) fun m d => m.insert d.name d.axioms
    let idx := evidence.after.index
    let restored := g.members.all fun (_, d, _) => restoredFor d (axiomsBySubstitution idx override d)
    if restored then
      pure (.accepted true true true, some (← IO.FS.readBinFile (c.target / file)),
        Json.mkObj [("method", toJson "walk")])
    else revert
  else
    let importerModules := (g.members.filterMap fun (_, d, _) =>
      (ctx.base.decls.find? (·.name == d)).map (·.module)).eraseDups.filter (· != module)
    let rec rebuildAll : List String → IO (Option (List Decl))
      | [] => pure (some [])
      | m :: rest => do
        match ← buildAndCertify m (c.fileOf m) with
        | none => pure none
        | some ds =>
          match ← rebuildAll rest with
          | none => pure none
          | some rest' => pure (some (ds ++ rest'))
    match ← rebuildAll importerModules with
    | none => revert
    | some importerDecls =>
      let importerFindings := compare ctx.aliases ctx.base
        { toolchain := ctx.base.toolchain, built := importerModules, decls := importerDecls } []
      if !importerFindings.isEmpty then revert else
      let allFresh := siteDecls ++ importerDecls
      let restored := g.members.all fun (_, d, _) =>
        restoredFor d (((allFresh.find? (·.name == d)).map (·.axioms)).getD [])
      if restored then
        pure (.accepted true true true, some (← IO.FS.readBinFile (c.target / file)),
          Json.mkObj [("method", toJson "rebuild"), ("rebuiltModules", toJson importerModules)])
      else revert

/-- Drive the single repair-frontier module of `s`'s fleet
(`docs/machine.md` § Level 3) to `FindingMending.next = .finish`: attempt
each head candidate (`attemptRepair`), commit an accepted one on the mend
branch (`commitAccepted`, with no decision-D11/D12 bookkeeping — a Level 3
candidate is never `.typeAnnotation` or `.followStatement`), and step the
machine with each verdict. Returns the `.built` state once the fleet's one
member is done. -/
partial def driveFindingMending (c : Ctx) (ctx : Context) (evidence : Evidence) (s : RunState) :
    IO RunState := do
  let .repairing _ _ _ _ f := s | return s
  let [mm] := f.mendings
    | throw <| IO.userError "lean-mend: the repair fleet does not hold exactly one FindingMending"
  match mm.next with
  | .finish => stepL c s (.repaired mm.module) "repaired" (toJson mm.module)
  | .giveUp g =>
    let s ← stepL c s (.repair mm.module .gaveUp) "repair"
      (Json.mkObj [("module", toJson mm.module), ("site", toJson g.key.site.1), ("action", toJson "gaveUp")])
    driveFindingMending c ctx evidence s
  | .attempt g cand =>
    let (obs, text?, detail) ← attemptRepair c ctx evidence g cand
    let s ← stepL c s (.repair mm.module obs) "repair"
      (Json.mkObj [("module", toJson mm.module), ("site", toJson g.key.site.1), ("rule", toJson cand.rule),
                   ("closes", toJson (g.members.map (·.2.1))), ("accepted", toJson text?.isSome),
                   ("detail", detail)])
    match text? with
    | some text =>
      let file := c.fileOf mm.module
      let mode := ((← git c.target #["ls-files", "--stage", "--", file.toString]).splitOn " ").head!
      commitAccepted c mm.module file mode text cand [] []
    | none => pure ()
    driveFindingMending c ctx evidence s

/-- The certificate, once no module is open with all its imports built: the
`certificate` observation (with the Level 3 candidate groups `sites3`
already built, `docs/machine.md` § Level 3), the D11 type-change warnings,
the evidence of the cards (`collectEvidence`, `docs/verification.md` §
What a card explains), the proof-only auto-accept of decision D16
(`autoAcceptProofOnly`), and the cards. A declaration with no certificate
row stops the run with `DeclUnread` (`c.stop`). `repairing` drives the
repair (`driveFindingMending`) and recurses: the certificate and its
evidence are gathered again once the repair-frontier module is done, since
its declarations may have changed. -/
partial def certify (c : Ctx) (s : RunState) : IO RunState := do
  let .built ctx st := s | return s
  let cert0 ← match ← certificate c.target c.toolchain
      (c.aliases.normalizeWith (Rule.prefixPairs c.rules)) c.files (statusList c st)
      (jobs := certificateJobs c.gate.limit c.gate.estimate) with
    | .ok cert => pure cert
    | .error x =>
      c.stop.modify (·.orElse fun _ => some (.declUnread x))
      throw <| IO.userError x.message
  let cert := { cert0 with followed := (← c.followedDecls.get).eraseDups }
  let head (dir : FilePath) : IO String := do
    pure ((← git dir #["rev-parse", "HEAD"]).splitOn "\n").head!
  let baseTree : Tree :=
    { dir := c.base, toolchain := ctx.base.toolchain.name, files := c.baseFiles,
      commit := ← head c.base, probe := probe c.base,
      request := c.base / ".lean-mend" / "explain.json" }
  let afterTree : Tree :=
    { dir := c.target, toolchain := c.toolchain, files := c.files, commit := ← head c.target,
      probe := probe c.target, request := c.target / ".lean-mend" / "explain.json" }
  let gatherEvidence (fs : List Finding) : IO Evidence :=
    collectEvidence (Names.ofAliases ctx.aliases) baseTree afterTree c.target c.start cert fs
  -- The open Violation findings and their evidence, gathered before the
  -- `certificate` observation, so the Core's guard can see whether any site
  -- has an unexhausted candidate (`docs/static-diff.md` § 6, decision S6).
  let fsPre := match RunState.compareClose ctx cert [] with
    | .ok fs => fs.filter (·.reason == .axiomsDiffer)
    | .error _ => []
  let repairEvidence ← if fsPre.isEmpty then pure none else some <$> gatherEvidence fsPre
  let sites3 ← match repairEvidence with
    | some e => buildSites3 c ctx cert e fsPre
    | none => pure []
  let next0 ← stepL c s (.certificate cert sites3) "certificate"
    (Json.mkObj [("built", toJson cert.built), ("decls", toJson cert.decls.length)])
  match next0, repairEvidence with
  | .repairing .., some e =>
    certify c (← driveFindingMending c ctx e next0)
  | .repairing .., none =>
    throw <| IO.userError "lean-mend: repairing with no Level 3 evidence"
  | _, _ =>
    for (d, why) in typeChanges ctx.aliases ctx.base cert do
      appendWarning c.ledger s!"type {d.name} in {d.module} {why} (decision D11)"
    let (_, fs0) := match next0 with
      | .awaiting _ _ r _ fs => (r, fs)
      | .done _ _ r _ => (r, [])
      | _ => ([], [])
    -- The evidence is gathered over every finding of the certificate, before
    -- a card is decided: the proof-only check (below) is itself a
    -- certification attempt (`docs/static-diff.md` § 6, decision S6), and it
    -- needs the bodies and proofs this evidence holds.
    let evidence ← if fs0.isEmpty then pure none else some <$> gatherEvidence fs0
    let next ← match evidence with
      | some e => autoAcceptProofOnly c ctx.aliases e next0
      | none => pure next0
    -- Computational equality (`docs/static-diff.md` § 4): certifyEqual on
    -- every Behavior finding decision D16's proof-only check left open,
    -- before any of them becomes a card (decision S6).
    let next ← autoAcceptCompEq c ctx.aliases baseTree afterTree next
    let (residue, fs) := match next with
      | .awaiting _ _ r _ fs => (r, fs)
      | .done _ _ r _ => (r, [])
      | _ => ([], [])
    let cards := fs.zipIdx.filterMap fun (f, i) =>
      f.reason.card.map fun k => ({ id := s!"c-{i + 1}", kind := k,
                                    subject := ctx.aliases.rename f.decl.name } : Card)
    saveSession c.target
      { target := c.target.toString, start := c.start, base := ctx.base, after := cert,
        mods := ctx.mods, aliases := ctx.aliases, residue, cards, evidence } fs
    pure next

/-- A new worktree for the mend of `m`, at `.lean-mend/mend/<m>`. Its commit
is the main checkout's working tree: `HEAD` plus the mended text of every
module whose mend ended and is not committed yet, so the worktree holds the
text of every module that `m` imports, as built (`docs/parallel.md` P8).
`git stash create` makes that commit with no change to the checkout, the
index or a ref; it prints nothing when the working tree equals `HEAD`. -/
def addWorktree (c : Ctx) (m : String) : IO FilePath := do
  let dir := c.target / ".lean-mend" / "mend" / m
  let stash := (← git c.target #["stash", "create"]).trimAscii.toString
  let base := if stash.isEmpty then "HEAD" else stash
  discard <| git c.target #["worktree", "add", "-q", "--detach", dir.toString, base]
  symlinkLakeDirs c dir
  pure dir

/-- What one background task of the dataflow schedule returns. -/
inductive Finished where
  /-- A module's mend ended. -/
  | plan (p : ModulePlan)
  /-- `lake build +module` ended. -/
  | build (module : String) (status : ModStatus)

/-- The shell's live view of the dataflow schedule (`docs/parallel.md` P8,
P13, P21). `live` runs ahead of the machine's own statuses: a module's mend
or build result enters `live` when its task ends, and enters the machine
when the driver replays it, in the canonical order. -/
structure Flow where
  live : Std.HashMap String ModStatus
  /-- Modules whose unblocking build started. -/
  builds : Std.HashSet String := {}
  /-- Modules whose mend started. -/
  mends : Std.HashSet String := {}
  running : List (Task (Except IO.Error Finished)) := []
  /-- The worktree of every mend that is still running. -/
  dirs : Std.HashMap String FilePath := {}
  /-- Ended mends that the driver did not replay yet. -/
  plans : Std.HashMap String ModulePlan := {}
  /-- Unblocking build results that the driver did not replay yet. -/
  unblocked : Std.HashMap String ModStatus := {}
  /-- Build results after a mend that the driver did not replay yet. -/
  checked : Std.HashMap String ModStatus := {}
  /-- The body rules of every ended mend (`docs/parallel.md` P22). -/
  rules : Std.HashMap String (List String) := {}

/-- `live` as `Statuses`. A module outside the run (Lean, a dependency)
builds. -/
def Flow.status (f : Flow) : Statuses := fun n => f.live.getD n .built

/-- Remove the worktree of every mend that did not end. -/
def removeMendWorktrees (c : Ctx) (f : Flow) : IO Unit := do
  for (_, d) in f.dirs do
    discard <| git c.target #["worktree", "remove", "--force", d.toString]

/-- Stop the schedule at the run's first error (fail fast, `docs/parallel.md`
P24). The caller throws that error after this returns, so the throw is in
its own `catch` branch (law LM5, `tests/CatchRethrow.lean`). The gate ends
every live probe and refuses every request that waits (`Gate.stop`), so each
running task ends: a task that waits for a probe's reply reads end of file.
The driver waits for every task, so that no Lean process outlives the run,
and removes the worktrees of the mends. The typed stop of the run (`c.stop`)
stays the one recorded before the error arrived: a probe that the stop ended
cannot replace it. -/
def stopSchedule (c : Ctx) (f : Flow) : IO Unit := do
  let first ← c.stop.get
  c.gate.stop
  for t in f.running do
    discard <| IO.wait t
  c.stop.set first
  removeMendWorktrees c f

/-- Start a task for every module that `Core.Run.ready` names on the live
statuses and that has no task yet (`docs/parallel.md` P8, P21): a `blocked`
module builds, and a `failing` module mends in a new worktree with its
followed-rule snapshot (P22). `opens` are the run's modules that were open
after the first build, in canonical order: only they can become ready.

A mend starts its probe only on an admission of `c.gate` (P24).
`Gate.acquire` gives a promise that the gate resolves when the measured tree
plus the probe budget fits the limit, in request order, so the modules get
their admissions in canonical order. The mend's task starts when the promise
resolves (`IO.mapTask`): until then the module holds no probe and no thread.
When the run stopped, the promise gives no admission, and the task ends with
an error. A build is running work of the gate (`Gate.spawn`). An error here
stops the schedule (`stopSchedule`), with the tasks that this call started. -/
def launch (c : Ctx) (ctx : Context) (opens : List Module) (f : Flow) : IO Flow := do
  let mut f := f
  for n in ready opens f.status do
    try
      match f.status n with
      | .blocked =>
        unless f.builds.contains n do
          let t ← c.gate.spawn (Finished.build n <$> buildModule c n)
          f := { f with builds := f.builds.insert n, running := f.running ++ [t] }
      | .failing =>
        unless f.mends.contains n do
          let dir ← addWorktree c n
          let followed := (importClosure c.order n).flatMap (f.rules.getD · [])
          let st := f.status
          let admission ← c.gate.acquire
          let t ← IO.mapTask (prio := .dedicated) (fun
              | some adm => Finished.plan <$> planSession c ctx st followed dir n adm
              | none => throw <| IO.userError s!"lean-mend: {n}: the run stopped before its probe started")
            admission.result!
          f := { f with mends := f.mends.insert n, dirs := f.dirs.insert n dir,
                        running := f.running ++ [t] }
      | _ => pure ()
    catch e => do stopSchedule c f; throw e
  pure f

/-- Take one task's result into `f` (`docs/parallel.md` P13). An ended mend
writes its text into the main checkout, and then the module builds, unless
it has residue: a residual module does not build, so no module that imports
it starts, as in the sequential run. No commit and no ledger line. -/
def settle (c : Ctx) (f : Flow) : Finished → IO Flow
  | .plan p => do
    IO.FS.writeBinFile (c.target / c.fileOf p.module) p.text
    discard <| git c.target #["worktree", "remove", "--force", p.dir.toString]
    let f := { f with plans := f.plans.insert p.module p, rules := f.rules.insert p.module p.bodyRules,
                      dirs := f.dirs.erase p.module }
    if p.residue then return { f with live := f.live.insert p.module .residual }
    let t ← c.gate.spawn (Finished.build p.module <$> buildModule c p.module)
    pure { f with running := f.running ++ [t] }
  | .build m s =>
    if f.mends.contains m then pure { f with checked := f.checked.insert m s, live := f.live.insert m s }
    else pure { f with unblocked := f.unblocked.insert m s, live := f.live.insert m s }

/-- The ledger detail of a `moduleBuild` observation. -/
def moduleBuildDetail (m : String) (s : ModStatus) : Json :=
  Json.mkObj [("module", toJson m), ("status", toJson (toString (repr s)))]

/-- Replay every result the canonical order can take now (`docs/parallel.md`
P10, P12). The next module is the head of `Core.Run.ready` on the machine's
own statuses. A `blocked` head needs its unblocking build result. A
`failing` head needs its plan and, when the plan has no residue, its build
result after the mend. The replay stops at the first head whose results
are not there yet. -/
partial def advance (c : Ctx) (opens : List Module) (f : Flow) (s : RunState) :
    IO (Flow × RunState) := do
  let .built _ st := s | return (f, s)
  let some n := (ready opens st).head? | return (f, s)
  match st n with
  | .blocked =>
    let some r := f.unblocked[n]? | return (f, s)
    let s ← stepL c s (.moduleBuild n r) "moduleBuild" (moduleBuildDetail n r)
    advance c opens { f with unblocked := f.unblocked.erase n } s
  | .failing =>
    let some p := f.plans[n]? | return (f, s)
    let check := f.checked[n]?
    if !p.residue && check.isNone then return (f, s)
    let s ← replayDiagnosed c s p
    let s ← replayRounds c s p
    let s ← match check with
      | some r => stepL c s (.moduleBuild n r) "moduleBuild" (moduleBuildDetail n r)
      | none => pure s
    advance c opens { f with plans := f.plans.erase n, checked := f.checked.erase n } s
  | other => throw <| IO.userError s!"lean-mend: the ready module {n} is {repr other}"

/-- The machine halted: wait for every running task, then remove the
worktrees of the mends. A task error stops the schedule (`stopSchedule`). -/
partial def endHalted (c : Ctx) (f : Flow) : IO Unit := do
  match f.running with
  | [] => removeMendWorktrees c f
  | t :: ts =>
    let (r, rest) ← IO.waitAny' (t :: ts)
    let f := { f with running := rest }
    match r with
    | .ok _ => endHalted c f
    | .error e => do stopSchedule c f; throw e

/-- The dataflow schedule (`docs/parallel.md` § Level 2): start every ready
module, replay what the canonical order can take, then wait for the next
task to end. It ends when no task runs. A halt ends the schedule: the
driver waits for the running tasks, so that no Lean process outlives the
run, and removes their worktrees (`endHalted`). The first error, of a task
or of the driver, stops the schedule at once (`stopSchedule`). -/
partial def dataflow (c : Ctx) (ctx : Context) (opens : List Module) (f : Flow) (s : RunState) :
    IO RunState := do
  let f ← launch c ctx opens f
  let (f, s) ← try
      let r ← advance c opens f s
      -- The replay freed the plans it took, so the gate checks its queue again.
      c.gate.recheck
      pure r
    catch e => do stopSchedule c f; throw e
  match s with
  | .built _ st =>
    match f.running with
    | [] =>
      if let some n := (ready opens st).head? then
        throw <| IO.userError s!"lean-mend: the dataflow schedule ended before the replay of {n}"
      pure s
    | t :: ts =>
      let (r, rest) ← IO.waitAny' (t :: ts)
      let f := { f with running := rest }
      match r with
      | .error e => do stopSchedule c f; throw e
      | .ok x =>
        let f ← try settle c f x catch e => do stopSchedule c f; throw e
        dataflow c ctx opens f s
  | _ =>
    endHalted c f
    pure s

/-- The level-1 run, after the first `build`. Termination is the theorem set
in `Spec/Termination.lean` (`openCount`, then `blockedCount`); the schedule
itself is `partial` because it runs IO. The dataflow schedule mends and
builds every module it can reach. Then one full `lake build` checks the
whole target against the machine's statuses, and the certificate follows. -/
def runModules (c : Ctx) (s : RunState) : IO RunState := do
  let .built ctx st := s | return s
  let opens := c.order.filter fun m => (st m.name).isOpen
  let live := Std.HashMap.ofList (c.order.map fun m => (m.name, st m.name))
  let s ← dataflow c ctx opens { live } s
  let .built _ st := s | return s
  let (_, built) ← buildAll c.target c.targets c.order
  let merged := overlay st built
  certify c (← stepL c s (.build merged) "build"
    (toJson ((statusList c merged).map fun (n, x) => s!"{n}: {repr x}")))

/-- Run the `--prepare` command in a tree before any Lake command there, for
example `lake exe cache get` when the target's own dependencies need fetching,
or a copy of a saved `.lake`. The first Lake command (the probe's `lake env`)
resolves the manifest and clones every package into a missing `.lake`, so a
prepare that runs after it finds the tree already populated. It must succeed. -/
def prepareTree (tree : FilePath) : List String → IO Unit
  | [] => pure ()
  | cmd :: args => discard <| runOk tree cmd args.toArray

/-- The baseline worktree `<target>/.lean-mend/base` at `HEAD~1`, and whether
it was reused. A worktree that a previous run left at the same commit, with no
change to a tracked file, is reused with its `.lake`: Lake's traces then
rebuild only what changed, so the reuse cannot give a stale build. Any other
state is removed and the worktree is added again, and only then `prepare`
runs, since a prepare (for example a copy of a saved `.lake`) is for a new
tree. -/
def baseTree (target : FilePath) (prepare : List String) : IO (FilePath × Bool) := do
  let base := target / ".lean-mend" / "base"
  let parent := ((← git target #["rev-parse", "HEAD~1"]).splitOn "\n").head!
  -- A crashed run can leave the worktree registered with its directory gone.
  discard <| git target #["worktree", "prune"]
  if ← base.pathExists then
    let head := ((← git base #["rev-parse", "HEAD"]).splitOn "\n").head!
    let clean := (← git base #["status", "--porcelain", "--untracked-files=no"]).isEmpty
    if head == parent && clean then return (base, true)
    discard <| git target #["worktree", "remove", "--force", base.toString]
  discard <| git target #["worktree", "add", "-q", "--detach", base.toString, parent]
  prepareTree base prepare
  pure (base, false)

/-- One tree's module graph, topological order and `buildAll`. -/
def graphAndBuild (tree : FilePath) (targets : List String) :
    IO (List (Module × FilePath) × List Module × List (String × ModStatus)) := do
  let files ← moduleGraph tree
  let order0 ← match topoOrder (files.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{tree}: {repr r}"
  let (order, built) ← buildAll tree targets order0
  pure (files, order, built)

/-- The bumped tree and the baseline, each set up and built, at the same time:
the two builds share no input (each runs `lake` in its own tree at its own
toolchain), so the run waits for the longer one, not for both. -/
def buildBoth (target : FilePath) (targets prepare : List String) :
    IO ((List (Module × FilePath) × List Module × List (String × ModStatus)) ×
        (FilePath × Bool × List (Module × FilePath) × List (String × ModStatus))) := do
  let baseTask ← IO.asTask (prio := .dedicated) do
    let (base, reused) ← baseTree target prepare
    let (files, _, built) ← graphAndBuild base targets
    pure (base, reused, files, built)
  let after ← (do prepareTree target prepare; graphAndBuild target targets).toBaseIO
  let base ← IO.wait baseTask
  -- Both results are read before either error propagates, so no build
  -- outlives the run.
  pure (← IO.ofExcept after, ← IO.ofExcept base)

/-- The baseline certificate, stored under `<target>/.lean-mend/base-cert/<key>.json`
(law LM3), and whether it came from the store. The key covers every input:
the baseline commit and toolchain, its built files (`builtContentHash`), its
module statuses, the normalization (alias pairs and rule prefixes), the probe
(`probeStamp`) and this lean-mend build (`selfHash`). A stored file is read
only under the same key. -/
def baseCertificate (target base : FilePath) (toolchain : String) (aliasPairs : List (String × String))
    (prefixes : List (String × String)) (norm : String → String) (files : List (Module × FilePath))
    (built : List (String × ModStatus)) (jobs : Nat) : IO (Except DeclUnread (Certificate × Bool)) := do
  let commit := ((← git base #["rev-parse", "HEAD"]).splitOn "\n").head!
  let parts : List String :=
    [commit, toolchain, ← builtContentHash base, probeStamp toolchain, ← selfHash,
     toString (built.map fun (n, s) => s!"{n}={repr s}"), toString aliasPairs, toString prefixes]
  let dir := target / ".lean-mend" / "base-cert"
  let file := dir / s!"{hash ("\n".intercalate parts)}.json"
  if ← file.pathExists then
    let cert ← parseOrThrow s!"base certificate {file}" (Json.parse (← IO.FS.readFile file) >>= certOf)
    return .ok (cert, true)
  match ← certificate base toolchain norm files built (jobs := jobs) with
  | .error x => pure (.error x)
  | .ok cert =>
    IO.FS.createDirAll dir
    IO.FS.writeFile file (certJson cert).compress
    pure (.ok (cert, false))

/-- The run's memory limit (`docs/parallel.md` P24): `--max-memory <GiB>`,
or else `MemAvailable` from `/proc/meminfo`, read one time at run start,
minus `reserveDefault`. -/
def memoryLimit : Option Nat → IO MemoryLimit
  | some gib => pure (.flag (KiB.ofGiB gib))
  | none => do
    let available ← parseOrThrow "/proc/meminfo" (Parse.memAvailable (← IO.FS.readFile "/proc/meminfo"))
    pure (.available available)

/-- The ledger detail of the run-start `memoryLimit` line: the limit, its
inputs, the charge of one work item, the hard cap of one probe, the kernel
limit on the whole tree, and the tree's measured size at run start. -/
def memoryLimitDetail (l : MemoryLimit) (cap : KiB) (treeLimit : TreeLimit) (tree : KiB) : Json :=
  let source := match l with
    | .flag _ => [("source", toJson "flag")]
    | .available a r => [("source", toJson "memAvailable"), ("memAvailableKiB", toJson a.val),
                         ("reserveKiB", toJson r.val)]
  Json.mkObj ([("limitKiB", toJson l.limit.val)] ++ source ++
    [("workEstimateKiB", toJson workEstimate.val), ("probeCapKiB", toJson cap.val),
     ("treeLimit", treeLimit.json), ("treeKiB", toJson tree.val)])

/-- `lean-mend run <target> --adopt [--targets <t,…>] [--prepare <cmd>] [--aliases-from <project>]…`
`maxMemory` is the `--max-memory <GiB>` flag; `none` computes the limit from
the available memory (`memoryLimit`). `probeCapMiB` is `--probe-cap <MiB>`;
`none` gives `probeCap`. A run that a probe stops at its cap ends with
`CapExceeded` (`docs/parallel.md` P24), and a certificate with no row for a
declaration ends it with `DeclUnread` (`docs/verification.md` § The
certificate). The ledger records each stop. -/
def runAdopt (target : FilePath) (targets : List String) (aliasesFrom : List FilePath)
    (prepare : List String := []) (rules : List Rule := []) (annotate : Bool := false)
    (follow : Bool := false) (speculate : Nat := defaultSpeculate) (maxMemory : Option Nat := none)
    (probeCapMiB : Option Nat := none) : IO (Except RunStop RunState) := do
  -- Absolute paths: git and lake run with the target as their working
  -- directory, so a relative path would resolve one level too deep.
  let target ← IO.FS.realPath target
  let aliasesFrom ← aliasesFrom.mapM IO.FS.realPath
  let status ← git target #["status", "--porcelain", "--untracked-files=no"]
  unless status.isEmpty do throw <| IO.userError s!"{target} has uncommitted changes"
  IO.FS.createDirAll (target / ".lean-mend")
  let ledger := target / ".lean-mend" / "ledger.jsonl"
  IO.FS.writeFile ledger ""
  -- The memory limit, one time, before the first child process starts.
  let limit ← memoryLimit maxMemory
  let probeCap := (probeCapMiB.map fun m => (⟨m * 1024⟩ : KiB)).getD probeCap
  let treeLimit ← setupTreeLimit limit.limit
  let gate ← Gate.new limit.limit workEstimate
  appendNote ledger "memoryLimit"
    (memoryLimitDetail limit probeCap treeLimit (← treePrivate (← procParents) gate.driver.toNat))
  let stop ← IO.mkRef none
  -- The bumped tree at HEAD and the baseline at HEAD~1, built at the same time
  -- (this also builds the dependencies of each).
  let toolchain := (← IO.FS.readFile (target / "lean-toolchain")).trimAscii.toString
  let ((files, order, built), (base, baseReused, baseFiles, baseBuilt)) ←
    buildBoth target targets prepare
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
  let baseToolchain := (← IO.FS.readFile (base / "lean-toolchain")).trimAscii.toString
  let (baseCert, certStored) ← match ← baseCertificate target base baseToolchain resolved.pairs
      (Rule.prefixPairs rules) (resolved.normalizeWith (Rule.prefixPairs rules)) baseFiles baseBuilt
      (certificateJobs gate.limit gate.estimate) with
    | .ok r => pure r
    | .error x =>
      let (name, fields) := (RunStop.declUnread x).note
      appendNote ledger name (Json.mkObj fields)
      return .error (.declUnread x)
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
                   follow, speculate, gate, probeCap, stop, followed, warned, followedDecls, ledger,
                   start := "", base, baseFiles }
  -- The machine, in its own order.
  let s ← stepL c (.idle target.toString) (.baseline baseCert baseFailing) "baseline"
    (Json.mkObj [("decls", toJson baseCert.decls.length), ("failing", toJson baseFailing),
                 ("worktreeReused", toJson baseReused), ("certificateStored", toJson certStored)])
  let s ← stepL c s (.bumped (order) raw) "bumped"
    (Json.mkObj [("aliases", toJson (resolved.pairs.map fun (a, b) => s!"{a} → {b}"))])
  let s ← stepL c s (.build (overlay (fun _ => .blocked) built)) "build"
    (toJson (built.map fun (n, x) => s!"{n}: {repr x}"))
  discard <| git target #["switch", "-q", "-c", "lean-mend/mend"]
  let start := ((← git target #["rev-parse", "HEAD"]).splitOn "\n").head!
  -- A probe that passes its cap, or a certificate with no row for a
  -- declaration, stops the run at once (fail fast): the schedule ends every
  -- live probe, waits for its tasks and throws (`stopSchedule`), and the
  -- typed stop names the module. Any other error stays an error.
  let final ← try runModules { c with start } s
    catch e => do
      let some x ← stop.get | throw e
      let (name, fields) := x.note
      appendNote ledger name (Json.mkObj fields)
      return .error x
  pure (.ok final)

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
