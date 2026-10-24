import LeanMend.Core.Graph
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

/-- Run one probe command inside the target. -/
def probe (target : FilePath) (args : Array String) : IO String := do
  IO.FS.createDirAll (target / ".lean-mend")
  IO.FS.writeFile (target / probePath) probeSource
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

/-- Build each module in graph order with `lake build <module>`. A module whose
target-internal import did not build is `blocked` and is not built. -/
def statuses (target : FilePath) (order : List Module) : IO (List (String × ModStatus)) := do
  let mut st : List (String × ModStatus) := []
  for m in order do
    let importsOk := m.imports.all fun i =>
      match st.lookup i with
      | some s => s == .built
      | none => true  -- outside the target: Lake builds it as a dependency
    if !importsOk then
      st := st ++ [(m.name, .blocked)]
    else
      let (code, _, _) ← run target "lake" #["build", m.name]
      st := st ++ [(m.name, if code == 0 then .built else .failing)]
  return st

/-- The certificate of the built modules (`docs/verification.md`). -/
def certificate (target : FilePath) (toolchain : String) (norm : String → String)
    (mods : List (Module × FilePath)) (st : List (String × ModStatus)) :
    IO Certificate := do
  let built := mods.filter fun (m, _) => st.lookup m.name == some .built
  let mut decls := []
  for (m, f) in built do
    let out ← probe target #["decls", m.name, f.toString]
    decls := decls ++ (← parseOrThrow s!"probe decls {m.name}" (Parse.lines (Parse.decl norm) out))
  pure { toolchain := ⟨toolchain⟩, built := built.map (·.1.name), decls }

/-- The byte offset of a `lean --json` position: `line` counts from 1 and
`column` counts code points from 0. -/
def byteOffset (src : String) (line column : Nat) : Nat :=
  let lines := src.splitOn "\n"
  let before := (lines.take (line - 1)).foldl (fun acc l => acc + l.utf8ByteSize + 1) 0
  before + (String.ofList ((lines.getD (line - 1) "").toList.take column)).utf8ByteSize

/-- Compile one module with `lake env lean --json` and read its errors as
sites, each with its candidates. Returns the error count and the open sites. -/
def diagnose (target : FilePath) (module : String) (file : FilePath)
    (cands : Site → List Candidate) : IO (Nat × List Open) := do
  let (_, out, _) ← run target "lake" #["env", "lean", "--json", file.toString]
  let ds ← parseOrThrow s!"lean --json {file}" (Parse.lines (Parse.diagnostic module) out)
  let errs := ds.filter (·.severity == .error)
  let src ← IO.FS.readFile (target / file)
  let sites := errs.map fun d =>
    { diagnostic := d, decl := none,
      start := byteOffset src d.line d.column,
      stop := byteOffset src d.endLine d.endColumn : Site }
  pure (errs.length, sites.map fun s => ⟨s, cands s⟩)

/-- Replace bytes `[c.start, c.stop)` of `file` with `c.replacement`. Returns
the previous content, for a revert. -/
def applyEdit (target : FilePath) (file : FilePath) (c : Candidate) : IO ByteArray := do
  let path := target / file
  let old ← IO.FS.readBinFile path
  IO.FS.writeBinFile path
    (old.extract 0 c.start ++ c.replacement.toUTF8 ++ old.extract c.stop old.size)
  pure old

end LeanMend.Shell
