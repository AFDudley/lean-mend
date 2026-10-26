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

By default (`--speculate 1`), an attempt runs in the target checkout, one
candidate at a time; a rejected candidate is reverted by restoring the
file's previous bytes. `--speculate <n>` attempts the next `n` head
candidates at the same time, each in its own worktree (`docs/parallel.md`
P14-P16, `consumeSpeculation`); the main checkout stays at the last accepted
commit until the Core picks a winner, in rule order.
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
expects (`docs/parallel.md` P14): `target` is the main checkout for a plain
attempt, or one attempt worktree's own copy for a speculative one. Returns the
file's previous bytes (for a revert on the main checkout), the `rebuilt`
observation, the `done` rule-name list `commitAccepted` and `warnFollow` need,
and the nodes at the attempted site. -/
def attemptOne (c : Ctx) (target : FilePath) (mm : Mending) (file : FilePath) (cand : Candidate) :
    IO (ByteArray × MendObs × List String × List (Site × List Node)) := do
  let saved ← applyEdit target file cand
  let done := (← c.followed.get) ++
    (match cand.target with | .body _ => [(cand.rule.splitOn ": ").head!] | _ => [])
  let (e, _, lints, opens0, nodesAt) ← diagnose target mm.module file c.aliases c.rules c.annotate c.follow
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

/-- One speculative attempt's result: the observation `Mending.step` must
see, the data `commitAccepted` needs if the Core accepts it, and the wall
time of its own rebuild, for the ledger (`docs/parallel.md` P14). -/
structure SpecResult where
  obs : MendObs
  done : List String
  nodesAt : List (Site × List Node)
  startedAt : Nat
  finishedAt : Nat

/-- Attempt every candidate of `items` in its own worktree, at the same time
(`docs/parallel.md` P14), then feed `Mending.step` their verdicts in rule
order (P15): a reject for every one that failed, then an accept at the first
that passed. Stops at the first accept, or when a verdict does not plainly
reject (a cleaning, or a refusal): the remaining precomputed results no
longer match the Core's state, so the batch ends there and the ordinary loop
resumes at the new head. Every result after the one it stops at is discarded
without being applied anywhere (P16): `consumeSpeculation` never touches the
main checkout except through `commitAccepted` at an accept. -/
partial def consumeSpeculation (c : Ctx) (m : String) (file : FilePath) :
    List (Candidate × FilePath × Task (Except IO.Error SpecResult)) → RunState → Mending →
      Nat → IO (RunState × Option Nat)
  | [], s, _, _ => pure (s, none)
  | (cd, dir, t) :: rest, s, mmCur, i => do
    let r ← IO.ofExcept t.get
    record c "speculateAttempt"
      (Json.mkObj [("index", toJson (i + 1)), ("worktree", toJson dir.toString),
                   ("rule", toJson cd.rule), ("startedAt", toJson r.startedAt),
                   ("finishedAt", toJson r.finishedAt)]) s
    let s' ← stepL c s (.mend m r.obs) "rebuilt" (rebuiltDetail cd.rule r.obs)
    match s' with
    | .mending _ _ f' =>
      let mm' ← soleMending f'
      if mm'.accepted.length > mmCur.accepted.length then
        -- The winning candidate was only ever applied in its own worktree
        -- (`docs/parallel.md` P14); the main checkout still holds the
        -- pre-attempt bytes, so apply it there before the commit.
        discard <| applyEdit c.target file cd
        commitAccepted c m file cd r.done r.nodesAt
        pure (s', some (i + 1))
      else if (mm'.sites.head?.map (·.candidates.length)) ==
          (mmCur.sites.head?.map fun o => o.candidates.length - 1) then
        consumeSpeculation c m file rest s' mm' (i + 1)
      else pure (s', none)
    | _ => pure (s', none)

/-- The level-1 loop, after `bumped`. Termination is the theorem set in
`Spec/Termination.lean`; the loop itself is `partial` because it runs IO. -/
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
    | m :: _ =>
      let done ← c.followed.get
      let (_, decls, _, opens, nodesAt) ← diagnose c.target m (c.fileOf m) c.aliases c.rules c.annotate c.follow
        (if c.follow then done else [])
      warnFollow c m done nodesAt
      -- Decision D11: without --annotate-binders, report the type narrowing
      -- the run would apply, and leave the site as residue.
      unless c.annotate do
        for o in opens do
          for t in typeCandidates o.site do
            appendWarning c.ledger s!"{m}:{o.site.diagnostic.line} {o.site.decl.getD "?"}: \
              would narrow `{o.site.text}` to `{t.replacement}`; rerun with --annotate-binders"
      let siteJson := opens.map fun o => Json.mkObj
        [("line", toJson o.site.diagnostic.line),
         ("class", toJson (toString (repr (classify o.site.diagnostic)))),
         ("decl", toJson o.site.decl),
         ("region", toJson (o.site.region.map fun r => toString (repr r))),
         ("candidates", toJson o.candidates.length)]
      loop c (← stepL c s (.diagnosed m decls opens) "diagnosed"
        (Json.mkObj [("module", toJson m), ("sites", toJson opens.length),
                     ("detail", Json.arr siteJson.toArray)]))
  | .mending _ _ f =>
    let mm ← soleMending f
    match mm.next with
    | .finish =>
      let s' ← stepL c s (.mended mm.module) "mended" (toJson mm.module)
      match s' with
      | .built _ st' =>
        let (_, built) ← buildAll c.target c.targets c.order
        let merged := overlay st' built
        loop c (← stepL c s' (.build merged) "build" (toJson ((statusList c merged).map fun (n, x) => s!"{n}: {repr x}")))
      | other => pure other
    | .giveUp site =>
      loop c (← stepL c s (.mend mm.module .gaveUp) "gaveUp"
        (Json.mkObj [("module", toJson mm.module), ("line", toJson site.diagnostic.line),
                     ("text", toJson site.diagnostic.text)]))
    | .attempt cand =>
      let file := c.fileOf mm.module
      if c.speculate ≤ 1 then
        -- The target checkout holds one attempt at a time, reverted on a
        -- reject (concept D3: attempts in worktrees are level 3 only).
        let (saved, obs, done, nodesAt) ← attemptOne c c.target mm file cand
        let s' ← stepL c s (.mend mm.module obs) "rebuilt" (rebuiltDetail cand.rule obs)
        let acceptedNow ← match s' with
          | .mending _ _ f' => do
            let mm' ← soleMending f'
            pure (decide (mm'.accepted.length > mm.accepted.length))
          | _ => pure false
        if acceptedNow then
          commitAccepted c mm.module file cand done nodesAt
        else
          IO.FS.writeBinFile (c.target / file) saved
        loop c s'
      else
        -- Speculation across the head site's candidates (`docs/parallel.md`
        -- P14-P16): the next `c.speculate` candidates, each in its own
        -- worktree, attempted at the same time.
        let cands := mm.speculate c.speculate
        let base := ((← git c.target #["rev-parse", "HEAD"]).splitOn "\n").head!
        let dirs := (List.range cands.length).map fun i => c.target / ".lean-mend" / s!"attempt-{i + 1}"
        -- `git worktree add` writes the shared `.git/worktrees` directory, so
        -- the driver serializes it; the rebuild each starts is what runs at
        -- the same time.
        for dir in dirs do
          discard <| git c.target #["worktree", "add", "-q", "--detach", dir.toString, base]
        record c "speculateRound"
          (Json.mkObj [("module", toJson mm.module), ("width", toJson c.speculate),
                       ("candidates", toJson cands.length),
                       ("worktrees", toJson (dirs.map FilePath.toString))]) s
        let items ← (dirs.zip cands).mapM fun (dir, cd) => do
          let t ← IO.asTask
            (do
              let startedAt ← IO.monoMsNow
              let (_, obs, done, nodesAt) ← attemptOne c dir mm file cd
              let finishedAt ← IO.monoMsNow
              pure { obs, done, nodesAt, startedAt, finishedAt : SpecResult })
            (prio := .dedicated)
          pure (cd, dir, t)
        let (s', acceptedIndex) ← consumeSpeculation c mm.module file items s mm 0
        record c "speculateResult"
          (Json.mkObj [("module", toJson mm.module), ("acceptedIndex", toJson acceptedIndex)]) s'
        for dir in dirs do
          discard <| git c.target #["worktree", "remove", "--force", dir.toString]
        record c "speculateCleanup" (Json.mkObj [("removed", toJson (dirs.map FilePath.toString))]) s'
        loop c s'
  | other => pure other

/-- Run the `--prepare` command in a tree before its build, for example
`lake exe cache get` when the target's own dependencies need fetching. It
must succeed. -/
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
  -- A crashed run can leave the worktree registered with its directory gone.
  discard <| git target #["worktree", "prune"]
  if ← base.pathExists then discard <| git target #["worktree", "remove", "--force", base.toString]
  discard <| git target #["worktree", "add", "-q", "--detach", base.toString, "HEAD~1"]
  let baseFiles ← moduleGraph base
  let baseOrder0 ← match topoOrder (baseFiles.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{repr r}"
  prepareTree base prepare
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
