import LeanMend.Core.Graph
import LeanMend.Core.Ops
import LeanMend.Shell.Parse

/-!
# The target

IO against one target: processes, the probe, Lake. See
`docs/architecture.md` § The version boundary and § Building the target.
Every command fails loud with its stderr (concept D6).
-/

namespace LeanMend.Shell

open System (FilePath)

/-- Run a command in `cwd`. Returns the exit code, stdout and stderr. -/
def run (cwd : FilePath) (cmd : String) (args : Array String) :
    IO (UInt32 × String × String) := do
  let o ← IO.Process.output { cmd, args, cwd }
  pure (o.exitCode, o.stdout, o.stderr)

/-- Run a command that must succeed; its stdout. -/
def runOk (cwd : FilePath) (cmd : String) (args : Array String) : IO String := do
  let (code, out, err) ← run cwd cmd args
  unless code == 0 do
    throw <| IO.userError s!"{cmd} {args} in {cwd} exited {code}:\n{err}{out}"
  pure out

/-- The probe source, compiled into lean-mend. The shell writes it into the
target, so the target's own toolchain compiles it (decision D3). -/
def probeSource : String := include_str "../../probe/Probe.lean"

def probePath : FilePath := ".lean-mend" / "Probe.lean"

/-- Write the probe source into `target`. It goes to a temporary file and is
renamed into place, so a probe that another task starts at the same time
never reads a file cut short (`certificate` runs probes in parallel, and each
module that mends starts its own `serve` process). -/
def writeProbe (target : FilePath) : IO Unit := do
  IO.FS.createDirAll (target / ".lean-mend")
  let tmp := target / ".lean-mend" / s!"Probe.lean.{← IO.monoNanosNow}.{← IO.rand 0 999999999}.tmp"
  IO.FS.writeFile tmp probeSource
  IO.FS.rename tmp (target / probePath)

/-- Run one probe command inside the target. -/
def probe (target : FilePath) (args : Array String) : IO String := do
  writeProbe target
  runOk target "lake" (#["env", "lean", "--run", probePath.toString] ++ args)

def parseOrThrow {α} (what : String) : Except String α → IO α
  | .ok v => pure v
  | .error e => throw <| IO.userError s!"{what}: {e}"

/-- The target's own `.lean` files: everything outside `.lake`, `.lean-mend`,
`.scratch`, `.git`, the lakefile, and any nested Lake package (a directory
with its own lakefile, such as a path dependency). -/
partial def sourceFiles (target : FilePath) : IO (List FilePath) := do
  let skip := [".lake", ".lean-mend", ".scratch", ".git"]
  let rec walk (dir : FilePath) (rel : FilePath) : IO (List FilePath) := do
    let mut acc := []
    for e in ← dir.readDir do
      let r := if rel.toString.isEmpty then FilePath.mk e.fileName else rel / e.fileName
      if ← e.path.isDir then
        let nested := (← (e.path / "lakefile.toml").pathExists) ||
          (← (e.path / "lakefile.lean").pathExists)
        unless skip.contains e.fileName || nested do acc := acc ++ (← walk e.path r)
      else if e.fileName.endsWith ".lean" && e.fileName != "lakefile.lean" then
        acc := acc ++ [r]
    return acc
  walk target ""

/-- Every nested Lake package under `target` (a path dependency's own
directory, the same test `sourceFiles` uses to stop there), at any depth —
`target` itself is not included. A module or speculative attempt worktree
symlinks each one's own `.lake` build directory from the main checkout
(`docs/parallel.md` P18, `Shell.Driver.symlinkLakeDirs`): a `git worktree
add` checkout holds every package's tracked source, never a package's
untracked build output. -/
partial def nestedPackageRoots (target : FilePath) : IO (List FilePath) := do
  let skip := [".lake", ".lean-mend", ".scratch", ".git"]
  let rec walk (dir : FilePath) (rel : FilePath) : IO (List FilePath) := do
    let mut acc := []
    for e in ← dir.readDir do
      if ← e.path.isDir then
        unless skip.contains e.fileName do
          let r := if rel.toString.isEmpty then FilePath.mk e.fileName else rel / e.fileName
          let nested := (← (e.path / "lakefile.toml").pathExists) ||
            (← (e.path / "lakefile.lean").pathExists)
          if nested then acc := acc ++ [r]
          acc := acc ++ (← walk e.path r)
    return acc
  walk target ""

/-- `Fx/Basic.lean` → `Fx.Basic`. -/
def moduleOfFile (f : FilePath) : String :=
  ".".intercalate ((f.withExtension "").components)

/-- The target's module graph, from the probe's `imports`. -/
def moduleGraph (target : FilePath) : IO (List (Module × FilePath)) := do
  let files ← sourceFiles target
  let out ← probe target (#["imports"] ++ files.toArray.map (·.toString))
  let rows ← parseOrThrow "probe imports" <| Parse.lines (fun j => do
    let f : String ← j.getObjValAs? String "file"
    let is : List String ← j.getObjValAs? (List String) "imports"
    pure (f, is)) out
  pure <| rows.map fun (f, is) => (⟨moduleOfFile f, is⟩, FilePath.mk f)

/-- The status of each module from one `lake build -v` (decision D4). Lake
prints one line per module job, in the same format from v4.29.0 to v4.35.0:
`Built M` or `Replayed M` means built, `✖ … Building M` means failing, and
`Ran M` with no build means an import failed, so `M` is blocked. A module that
Lake names in no line is not required by the targets, so it is outside the run
and is dropped from `order`. Returns the order restricted to the run, and the
statuses. -/
def buildAll (target : FilePath) (targets : List String) (order : List Module) :
    IO (List Module × List (String × ModStatus)) := do
  let (_, out, err) ← run target "lake" (#["build", "-v"] ++ targets.toArray)
  let names := order.map (·.name)
  let mut seen : List (String × ModStatus) := []
  for line in (out ++ "\n" ++ err).splitOn "\n" do
    let ws := (line.splitOn " ").filter (· ≠ "")
    -- ws: [symbol, "[i/n]", verb, module, …]
    match ws with
    | sym :: _ :: verb :: m :: _ =>
      if names.contains m then
        let st? : Option ModStatus :=
          if verb == "Built" || verb == "Replayed" then some .built
          else if verb == "Building" && sym == "✖" then some .failing
          else if verb == "Ran" then some .blocked
          else none
        if let some st := st? then
          -- A module can appear more than once; built or failing wins over Ran.
          seen := match seen.lookup m with
            | some .built | some .failing => seen
            | _ => (m, st) :: seen.filter (·.1 != m)
    | _ => pure ()
  let inRun := order.filter (fun m => (seen.lookup m.name).isSome)
  pure (inRun, inRun.map fun m => (m.name, (seen.lookup m.name).getD .blocked))

/-- `l` in consecutive parts of at most `n` elements (`n` = 0 means one part). -/
def chunks {α} (n : Nat) (l : List α) : List (List α) :=
  if n = 0 then (if l.isEmpty then [] else [l]) else
  let step := fun (acc : List (List α)) (x : α) => match acc with
    | cur :: rest => if cur.length < n then (x :: cur) :: rest else [x] :: acc
    | [] => [[x]]
  ((l.foldl step []).map List.reverse).reverse

/-- The module that Lean names in an import clash, "import X failed,
environment already contains 'n' from Y": `X`, the module it could not add. -/
def clashModule (err : String) : Option String := do
  let after ← (err.splitOn "import ").getLast?
  let x := (after.splitOn " failed, environment already contains").head!
  if x == after then none else some x

/-- The module of one certificate line. -/
def lineModule : Except DeclUnread Decl → String
  | .ok d => d.module
  | .error x => x.module

/-- The certificate lines of `part` from the probe's `decls-batch`, which
imports the modules of `part` into one environment: a row, or a declaration
the probe could not read (`Parse.declLine`). Two modules that declare the same
name, for example `main` of two executables or a constant that `native_decide`
generates in two copies of one block, each build, but Lean refuses to import
both: "import X failed, environment already contains 'n' from Y". The probe
then runs again without `X`, so each clash costs one probe run, and the moved
modules form a part of their own. A module that built can be imported by
itself, so a clash that names no other module of the part, and any other
error, halts at once.

The environment of a part holds every module of the part, so it can hold a
token that the imports of one module do not declare, and that module's file
then does not parse (`docs/verification.md` § The certificate). So a module
with an `unread` line in a part of two or more modules is read again alone,
in a part of its own, which has the module's own environment. The lines of
that run replace its lines; an `unread` line there stands. -/
partial def declsOf (target list : FilePath) (norm : String → String)
    (part : List (Module × FilePath)) : IO (List (Except DeclUnread Decl)) := do
  let rec go (cur moved : List (Module × FilePath)) :
      IO (String × List (Module × FilePath)) := do
    IO.FS.writeFile list ("\n".intercalate (cur.map fun (m, f) => s!"{m.name}\t{f}"))
    try
      let out ← probe target #["decls-batch", list.toString]
      pure (out, moved)
    catch e =>
      let some x := clashModule e.toString | throw e
      unless cur.length > 1 && cur.any (·.1.name == x) do throw e
      go (cur.filter (·.1.name != x)) (moved ++ cur.filter (·.1.name == x))
  let (out, moved) ← go part []
  let lines ← parseOrThrow "probe decls-batch" (Parse.lines (Parse.declLine norm) out)
  let cur := part.filter fun (m, _) => !moved.any (·.1.name == m.name)
  let alone := if cur.length > 1 then
      cur.filter fun (m, _) => lines.any fun l => l matches .error _ && lineModule l == m.name
    else []
  let mut decls := lines.filter fun l => !alone.any (·.1.name == lineModule l)
  for mf in alone do
    decls := decls ++ (← declsOf target list norm [mf])
  if moved.isEmpty then return decls
  return decls ++ (← declsOf target list norm moved)

/-- The certificate of the built modules (`docs/verification.md`). The probe
reads `chunk` modules per process, from one environment (`declsOf`), and up to
`jobs` processes run at once, each with its own list file. One probe process
holds about 4 GB on EquiVM, so the default stays at 4. The rows keep the order
of the chunks.

Every declaration that the certificate selects must have a row. When the
probe cannot give one, the result is the first such declaration, after the
wave of probe processes that found it, and no certificate (fail fast). -/
def certificate (target : FilePath) (toolchain : String) (norm : String → String)
    (mods : List (Module × FilePath)) (st : List (String × ModStatus))
    (chunk : Nat := 200) (jobs : Nat := 4) : IO (Except DeclUnread Certificate) := do
  let built := mods.filter fun (m, _) => st.lookup m.name == some .built
  let parts := (chunks chunk built).toArray
  let mut decls : Array Decl := #[]
  for wave in chunks jobs (List.range parts.size) do
    let tasks ← wave.mapM fun i =>
      let list := target / ".lean-mend" / s!"decls-batch-{i}.txt"
      IO.asTask (declsOf target list norm parts[i]!) (prio := .dedicated)
    let lines ← tasks.mapM fun t => do IO.ofExcept (← IO.wait t)
    for line in lines.flatten do
      match line with
      | .ok d => decls := decls.push d
      | .error x => return .error x
  pure (.ok { toolchain := ⟨toolchain⟩, built := built.map (·.1.name), decls := decls.toList })

/-- The byte offset of a `lean --json` position: `line` counts from 1 and
`column` counts code points from 0. -/
def byteOffset (src : String) (line column : Nat) : Nat :=
  let lines := src.splitOn "\n"
  let before := (lines.take (line - 1)).foldl (fun acc l => acc + l.utf8ByteSize + 1) 0
  before + (String.ofList ((lines.getD (line - 1) "").toList.take column)).utf8ByteSize

/-- One declaration command of a file, from the probe's `regions`. -/
structure DeclRegion where
  name : String
  range : Nat × Nat
  statement : Nat × Nat
  body : Nat × Nat

/-- One `regions`-shaped JSON object (a line of the probe's `regions`
command, or one entry of a probe serve reply's `"regions"` array) as a
`DeclRegion`. -/
def declRegionOf (j : Lean.Json) : Except String DeclRegion := do
  let pair (k : String) : Except String (Nat × Nat) := do
    match ← j.getObjValAs? (List Nat) k with
    | [a, b] => pure (a, b)
    | _ => throw s!"field '{k}' is not a byte range"
  pure { name := ← j.getObjValAs? String "name", range := ← pair "range",
         statement := ← pair "statementRange", body := ← pair "bodyRange" }

/-- The declaration and region that hold byte offset `pos`, with the
declaration's index among `rs` in source order (`docs/parallel.md` X1). -/
def locate (rs : List DeclRegion) (pos : Nat) :
    Option String × Option SiteRegion × Option Nat × Option (Nat × Nat) × Option (Nat × Nat) ×
      Option (Nat × Nat) × Option Nat :=
  let inside (r : Nat × Nat) := r.1 ≤ pos && pos < r.2
  match rs.zipIdx.find? (inside ·.1.range) with
  | none => (none, none, none, none, none, none, none)
  | some (d, i) =>
    let name := if d.name.isEmpty then none else some d.name
    (name, (if inside d.body then some .body
            else if inside d.statement then some .statement else none), some d.range.1,
     some d.body, some d.statement, some d.range, some i)

/-- The text that Lean writes when its resident size passes the `-M` cap
(`check_memory` in the Lean runtime). -/
def overCapText : String := "excessive memory consumption detected"

/-- A long-lived probe process for one module (`docs/parallel.md` C1, C4): it
serves every `probeElaborate` and `probeServe` request of every attempt on
the module, started by `probeServeStart` and stopped by `probeServeStop`. It
keeps the module's last elaboration, so each attempt elaborates again only
from the first command that the attempt's text changed. `exited` holds the
exit code once a wait reaped the process: the operating system then knows the
process no more, so a second wait fails with `ECHILD`.

The memory cap (`docs/parallel.md` P24): the probe runs under `lean -M`, so
Lean stops it with "excessive memory consumption detected" when its resident
size passes `cap`. `peak` is the probe's peak resident size from its last
reply, and `overCap` records that Lean stopped the probe at its cap.

The session keeps `child` with its stdin, and the stop ends the process
group (`killProbe`). `IO.Process.Child.takeStdin` returns a child that does
not know that it started with `setsid` (Lean v4.35.0, measured on kelce on
2026-11-06): its `kill` then signals `lake env` only, and the `lean` child
lives on with the probe's stdout open. -/
structure ProbeSession where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  exited : IO.Ref (Option UInt32)
  /-- The probe's stderr, read to its end (`readStderr`). -/
  stderr : Task (Except IO.Error String)
  cap : KiB
  peak : IO.Ref KiB
  overCap : IO.Ref Bool

/-- End the probe process `child` and every process in its group with
`SIGKILL` (`IO.Process.Child.kill`). `probeServeStart` starts the probe in
its own session (`setsid`), so the group is the whole probe: `lake env` and
its `lean` child. Both hold the probe's stdout, so a reader of it then reads
end of file. A group that ended already needs no signal: the kill then fails
with "no such process", and this function returns. -/
def killProbe {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  try child.kill
  catch
    | .noSuchThing .. => pure ()
    | e => throw e

/-- Read `h`, a probe's stderr, to its end. Each line also goes to
lean-mend's own stderr, as before. A task reads it from the start, so the
pipe never fills and never blocks the probe. At a line that holds
`overCapText`, Lean stopped the probe at its cap (`docs/parallel.md` P24):
`overCap` is set and `stop` runs at once. A probe can write that text and
then not exit (`tests/cap-stop.sh`), so the shell does not wait for its
exit. -/
partial def readStderr (h : IO.FS.Handle) (overCap : IO.Ref Bool) (stop : IO Unit) : IO String := do
  let rec go (acc : String) : IO String := do
    let line ← h.getLine
    if line.isEmpty then return acc
    IO.eprint line
    if (line.splitOn overCapText).length > 1 then
      overCap.set true
      stop
    go (acc ++ line)
  go ""

/-- A session for a probe process `child` with the cap `cap`. At the cap
text on its stderr, the session ends the probe (`readStderr`, `killProbe`)
and then runs `onCap` with the probe's peak at its last reply. -/
def ProbeSession.ofChild (child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped })
    (cap : KiB) (onCap : KiB → IO Unit) : IO ProbeSession := do
  let overCap ← IO.mkRef false
  let peak ← IO.mkRef ⟨0⟩
  let stderr ← IO.asTask (prio := .dedicated) <| readStderr child.stderr overCap do
    killProbe child
    onCap (← peak.get)
  pure { child, exited := ← IO.mkRef none, stderr, cap, peak, overCap }

/-- Start one probe process inside `target`, running the probe's `serve`
command (`docs/parallel.md` C1) under `lean -M` at `cap` (P24). The probe
starts in its own session (`setsid`), so `killProbe` ends `lake env` and its
`lean` child together. `onCap` runs when Lean stopped the probe at its cap
(`ProbeSession.ofChild`). -/
def probeServeStart (target : FilePath) (cap : KiB) (onCap : KiB → IO Unit) : IO ProbeSession := do
  writeProbe target
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["env", "lean", "-M", toString cap.toMiB, "--run", probePath.toString,
                               "serve"],
      cwd := target, stdin := .piped, stdout := .piped, stderr := .piped, setsid := true }
  ProbeSession.ofChild child cap onCap

/-- One request-reply round trip of `s`'s probe process. A probe that ends
with no reply is reaped here, its exit code goes in `s.exited`, and the error
holds its stderr. The wait for the end of the stderr comes first: a stderr
reader that saw the cap text ends the probe's group before the reap. -/
def probeServeRequest (s : ProbeSession) (file : FilePath) (req : Lean.Json) : IO Lean.Json := do
  if (← s.exited.get).isSome then throw <| IO.userError s!"probe serve: the probe for {file} is stopped"
  s.child.stdin.putStrLn req.compress
  s.child.stdin.flush
  let line ← s.child.stdout.getLine
  if line.isEmpty then
    let err ← IO.ofExcept (← IO.wait s.stderr)
    let code ← s.child.wait
    s.exited.set (some code)
    throw <| IO.userError s!"probe serve: process exited {code} with no reply for {file}; its stderr:\n{err}"
  match Lean.Json.parse line with
  | .ok j =>
    if let .ok p := j.getObjValAs? Nat "peakKiB" then s.peak.set ⟨p⟩
    pure j
  | .error e => throw <| IO.userError s!"probe serve reply for {file}: {e}"

/-- End `s`'s probe from the outside (`Gate.stop`): end its process group,
unless a wait reaped the probe. A task that waits for a reply of the probe
then reads end of file, and its request reaps the probe. -/
def probeServeKill (s : ProbeSession) : IO Unit := do
  if (← s.exited.get).isSome then return
  killProbe s.child

/-- Stop `s`'s probe process: end its process group (`killProbe`), then wait
for the end of its stderr and reap it. The probe keeps nothing that the shell
needs after its last reply, so the stop is the kill. A process that a request
already reaped (`s.exited`) is not waited for again: a second wait fails with
`ECHILD`, and that error would replace the request's own error. -/
def probeServeStop (s : ProbeSession) : IO Unit := do
  if (← s.exited.get).isSome then return
  killProbe s.child
  discard <| IO.ofExcept (← IO.wait s.stderr)
  s.exited.set (some (← s.child.wait))

/-- The declaration regions and the node paths at `offsets`, for the current
text of `file`, from `s`'s one probe process (`docs/parallel.md` C1-C3): one
`syntax` request in place of the two separate `regions` and `node` probe
runs. -/
def probeServe (s : ProbeSession) (target : FilePath) (file : FilePath) (offsets : List Nat) :
    IO (List DeclRegion × List (Nat × List Node)) := do
  let src ← IO.FS.readFile (target / file)
  let reply ← probeServeRequest s file <| Lean.Json.mkObj
    [("op", Lean.toJson "syntax"), ("file", Lean.toJson file.toString), ("offsets", Lean.toJson offsets)]
  let rs ← parseOrThrow s!"probe serve regions {file}" <| do
    let arr : List Lean.Json ← reply.getObjValAs? (List Lean.Json) "regions"
    arr.mapM declRegionOf
  let ns ← parseOrThrow s!"probe serve nodes {file}" <| do
    let arr : List Lean.Json ← reply.getObjValAs? (List Lean.Json) "nodes"
    arr.mapM (Parse.nodes src)
  pure (rs, ns)

/-- The diagnostics of `lake env lean --json <file>` for the current text of
`file`, from `s`'s one probe process (`docs/parallel.md` C4, C5): one
`elaborate` request. The probe elaborates the text with the same processor
and options as `lean --json`, and reuses its previous elaboration of `file`
up to the first changed command. A reverted edit is one more change: the next
request sends the earlier text again. -/
def probeElaborate (s : ProbeSession) (module : String) (file : FilePath) : IO (List Diagnostic) := do
  let reply ← probeServeRequest s file <| Lean.Json.mkObj
    [("op", Lean.toJson "elaborate"), ("file", Lean.toJson file.toString)]
  parseOrThrow s!"probe serve messages {file}" <| do
    let arr : List Lean.Json ← reply.getObjValAs? (List Lean.Json) "messages"
    arr.mapM (Parse.diagnostic module)

/-- Elaborate one module and read its errors as sites, each with its
declaration, region and candidates. The diagnostics are those of
`lake env lean --json` (`docs/parallel.md` C5), from an `elaborate` request
to `session`'s probe process, which elaborates again only from the first
changed command (C4). The probe reads the syntax nodes only at sites whose
class some rule answers, and returns them together with the whole file's
declaration regions in one `syntax` request (C1-C3): the node offsets come
from the diagnostics themselves, not from the regions, so both are known
before either probe result is needed. Returns the error count, the module's
declaration count (`docs/parallel.md` X6), the linter warnings (kind
`linter.*`) with their byte offsets and, for an unused simp argument, its
name, and the open sites. -/
def diagnose (session : ProbeSession) (target : FilePath) (module : String) (file : FilePath)
    (aliases : AliasMap) (rules : List Rule) (annotate follow : Bool) (followed : List String) :
    IO (Nat × Nat × List (Nat × Option String) × List Open × List (Site × List Node)) := do
  let ds ← probeElaborate session module file
  let errs := ds.filter (·.severity == .error)
  let src ← IO.FS.readFile (target / file)
  -- Each linter warning: its byte offset, and for `linter.unusedSimpArgs` the
  -- argument Lean names ("This simp argument is unused:\n  x").
  let lints := (ds.filter fun d => d.severity == .warning && d.kind.startsWith "linter.").map
    fun d =>
      let arg := if d.kind == "linter.unusedSimpArgs" then
        ((d.text.splitOn "\n").drop 1).head?.map (·.trimAscii.toString) else none
      (byteOffset src d.line d.column, arg)
  -- An error range can cover a whole tactic block (`unsolved goals` is
  -- reported at `by`), so the probe reads the nodes at the range's start and
  -- its end.
  let rawLast (start stop : Nat) := if stop > start then stop - 1 else start
  let offsetsOf (d : Diagnostic) : Nat × Nat :=
    (byteOffset src d.line d.column, byteOffset src d.endLine d.endColumn)
  let wantedOffsets := (errs.filter fun d => rules.any (·.cls == classify d)).flatMap fun d =>
    let (start, stop) := offsetsOf d
    [start, rawLast start stop]
  let (rs, nodes) ← if errs.isEmpty then pure ([], []) else
    probeServe session target file wantedOffsets.eraseDups
  let sites := errs.map fun d =>
    let (start, stop) := offsetsOf d
    let (decl, region, declStart, bodyR, stmtR, declR, declIdx) := locate rs start
    let bytes := src.toUTF8
    { diagnostic := d, decl, region, declStart, start, stop, file := src,
      text := String.fromUTF8! (bytes.extract start stop),
      body := bodyR.map fun (a, b) => (a, String.fromUTF8! (bytes.extract a b)),
      statement := stmtR.map fun (a, b) => (a, String.fromUTF8! (bytes.extract a b)),
      declText := declR.map fun (a, b) => (a, String.fromUTF8! (bytes.extract a b)),
      declIndex := declIdx.getD 0 : Site }
  let last (s : Site) := if s.stop > s.start then s.stop - 1 else s.start
  let at_ (o : Nat) := (nodes.lookup o).getD []
  pure (errs.length, rs.length, lints,
    sites.map (fun s => ⟨s, proposeAll aliases rules (at_ s.start ++ at_ (last s)) annotate follow followed s⟩),
    sites.map fun s => (s, at_ s.start ++ at_ (last s)))

/-- `old` with bytes `[c.start, c.stop)` replaced by `c.replacement`. -/
def spliceEdit (old : ByteArray) (c : Candidate) : ByteArray :=
  old.extract 0 c.start ++ c.replacement.toUTF8 ++ old.extract c.stop old.size

/-- Replace bytes `[c.start, c.stop)` of `file` with `c.replacement`. Returns
the previous content, for a revert. -/
def applyEdit (target : FilePath) (file : FilePath) (c : Candidate) : IO ByteArray := do
  let path := target / file
  let old ← IO.FS.readBinFile path
  IO.FS.writeBinFile path (spliceEdit old c)
  pure old

end LeanMend.Shell
