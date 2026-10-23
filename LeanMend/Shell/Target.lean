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
`.scratch`, `.git` and the lakefile. -/
partial def sourceFiles (target : FilePath) : IO (List FilePath) := do
  let skip := [".lake", ".lean-mend", ".scratch", ".git"]
  let rec walk (dir : FilePath) (rel : FilePath) : IO (List FilePath) := do
    let mut acc := []
    for e in ← dir.readDir do
      let r := if rel.toString.isEmpty then FilePath.mk e.fileName else rel / e.fileName
      if ← e.path.isDir then
        unless skip.contains e.fileName do acc := acc ++ (← walk e.path r)
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
def certificate (target : FilePath) (toolchain : String)
    (mods : List (Module × FilePath)) (st : List (String × ModStatus)) :
    IO Certificate := do
  let built := mods.filter fun (m, _) => st.lookup m.name == some .built
  let mut decls := []
  for (m, f) in built do
    let out ← probe target #["decls", m.name, f.toString]
    decls := decls ++ (← parseOrThrow s!"probe decls {m.name}" (Parse.lines Parse.decl out))
  pure { toolchain := ⟨toolchain⟩, built := built.map (·.1.name), decls }

end LeanMend.Shell
