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

/-- Run one probe command inside the target. The probe source goes to a
temporary file and is renamed into place, so a probe that another task starts
at the same time never reads a file cut short (`certificate` runs probes in
parallel). -/
def probe (target : FilePath) (args : Array String) : IO String := do
  IO.FS.createDirAll (target / ".lean-mend")
  let tmp := target / ".lean-mend" / s!"Probe.lean.{← IO.monoNanosNow}.{← IO.rand 0 999999999}.tmp"
  IO.FS.writeFile tmp probeSource
  IO.FS.rename tmp (target / probePath)
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
`target` itself is not included. A wave or speculative attempt worktree
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

/-- The declarations of `part` from the probe's `decls-batch`, which imports
the modules of `part` into one environment. Two modules that declare the same
name, for example `main` of two executables or a constant that `native_decide`
generates in two copies of one block, each build, but Lean refuses to import
both: "import X failed, environment already contains 'n' from Y". The probe
then runs again without `X`, so each clash costs one probe run, and the moved
modules form a part of their own. A module that built can be imported by
itself, so a clash that names no other module of the part, and any other
error, halts at once. -/
partial def declsOf (target list : FilePath) (norm : String → String)
    (part : List (Module × FilePath)) : IO (List Decl) := do
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
  let decls ← parseOrThrow "probe decls-batch" (Parse.lines (Parse.decl norm) out)
  if moved.isEmpty then return decls
  return decls ++ (← declsOf target list norm moved)

/-- The certificate of the built modules (`docs/verification.md`). The probe
reads `chunk` modules per process, from one environment (`declsOf`), and up to
`jobs` processes run at once, each with its own list file. One probe process
holds about 4 GB on EquiVM, so the default stays at 4. The rows keep the order
of the chunks. -/
def certificate (target : FilePath) (toolchain : String) (norm : String → String)
    (mods : List (Module × FilePath)) (st : List (String × ModStatus))
    (chunk : Nat := 200) (jobs : Nat := 4) : IO Certificate := do
  let built := mods.filter fun (m, _) => st.lookup m.name == some .built
  let parts := (chunks chunk built).toArray
  let mut decls : Array (List Decl) := #[]
  for wave in chunks jobs (List.range parts.size) do
    let tasks ← wave.mapM fun i =>
      let list := target / ".lean-mend" / s!"decls-batch-{i}.txt"
      IO.asTask (declsOf target list norm parts[i]!) (prio := .dedicated)
    for t in tasks do
      decls := decls.push (← IO.ofExcept (← IO.wait t))
  pure { toolchain := ⟨toolchain⟩, built := built.map (·.1.name), decls := decls.toList.flatten }

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

def readRegions (target : FilePath) (file : FilePath) : IO (List DeclRegion) := do
  let out ← probe target #["regions", file.toString]
  let pair (j : Lean.Json) (k : String) : Except String (Nat × Nat) := do
    match ← j.getObjValAs? (List Nat) k with
    | [a, b] => pure (a, b)
    | _ => throw s!"field '{k}' is not a byte range"
  parseOrThrow s!"probe regions {file}" <| Parse.lines (fun j => do
    pure { name := ← j.getObjValAs? String "name", range := ← pair j "range",
           statement := ← pair j "statementRange", body := ← pair j "bodyRange" }) out

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

/-- The probe's `node` output for some offsets of one file, in one process. -/
def readNodes (target : FilePath) (file : FilePath) (offsets : List Nat) :
    IO (List (Nat × List Node)) := do
  if offsets.isEmpty then return []
  let src ← IO.FS.readFile (target / file)
  let out ← probe target (#["node", file.toString] ++ offsets.toArray.map toString)
  parseOrThrow s!"probe node {file}" (Parse.lines (Parse.nodes src) out)

/-- Compile one module with `lake env lean --json` and read its errors as
sites, each with its declaration, region and candidates. The probe reads the
syntax nodes only at sites whose class some rule answers. Returns the error
count, the module's declaration count (`docs/parallel.md` X6), the linter
warnings (kind `linter.*`) with their byte offsets and, for an unused simp
argument, its name, and the open sites. -/
def diagnose (target : FilePath) (module : String) (file : FilePath)
    (aliases : AliasMap) (rules : List Rule) (annotate follow : Bool) (followed : List String) :
    IO (Nat × Nat × List (Nat × Option String) × List Open × List (Site × List Node)) := do
  let (_, out, _) ← run target "lake" #["env", "lean", "--json", file.toString]
  let ds ← parseOrThrow s!"lean --json {file}" (Parse.lines (Parse.diagnostic module) out)
  let errs := ds.filter (·.severity == .error)
  let src ← IO.FS.readFile (target / file)
  -- Each linter warning: its byte offset, and for `linter.unusedSimpArgs` the
  -- argument Lean names ("This simp argument is unused:\n  x").
  let lints := (ds.filter fun d => d.severity == .warning && d.kind.startsWith "linter.").map
    fun d =>
      let arg := if d.kind == "linter.unusedSimpArgs" then
        ((d.text.splitOn "\n").drop 1).head?.map (·.trimAscii.toString) else none
      (byteOffset src d.line d.column, arg)
  let rs ← if errs.isEmpty then pure [] else readRegions target file
  let sites := errs.map fun d =>
    let start := byteOffset src d.line d.column
    let (decl, region, declStart, bodyR, stmtR, declR, declIdx) := locate rs start
    let stop := byteOffset src d.endLine d.endColumn
    let bytes := src.toUTF8
    { diagnostic := d, decl, region, declStart, start, stop, file := src,
      text := String.fromUTF8! (bytes.extract start stop),
      body := bodyR.map fun (a, b) => (a, String.fromUTF8! (bytes.extract a b)),
      statement := stmtR.map fun (a, b) => (a, String.fromUTF8! (bytes.extract a b)),
      declText := declR.map fun (a, b) => (a, String.fromUTF8! (bytes.extract a b)),
      declIndex := declIdx.getD 0 : Site }
  -- An error range can cover a whole tactic block (`unsolved goals` is reported
  -- at `by`), so the probe reads the nodes at the range's start and its end.
  let last (s : Site) := if s.stop > s.start then s.stop - 1 else s.start
  let wanted := sites.filter fun s => rules.any (·.cls == classify s.diagnostic)
  let nodes ← readNodes target file (wanted.flatMap fun s => [s.start, last s]).eraseDups
  let at_ (o : Nat) := (nodes.lookup o).getD []
  pure (errs.length, rs.length, lints,
    sites.map (fun s => ⟨s, proposeAll aliases rules (at_ s.start ++ at_ (last s)) annotate follow followed s⟩),
    sites.map fun s => (s, at_ s.start ++ at_ (last s)))

/-- Replace bytes `[c.start, c.stop)` of `file` with `c.replacement`. Returns
the previous content, for a revert. -/
def applyEdit (target : FilePath) (file : FilePath) (c : Candidate) : IO ByteArray := do
  let path := target / file
  let old ← IO.FS.readBinFile path
  IO.FS.writeBinFile path
    (old.extract 0 c.start ++ c.replacement.toUTF8 ++ old.extract c.stop old.size)
  pure old

end LeanMend.Shell
