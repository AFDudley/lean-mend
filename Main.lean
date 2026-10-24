import LeanMend
import LeanMend.Shell.Target
import LeanMend.Shell.Driver

/-!
# The `lean-mend` executable

The composition root is not built yet (`docs/architecture.md`, Driver.lean).
This entry point runs the first transition of the machine against a real
target:

    lean-mend baseline <target>

It reads the module graph, builds each module in graph order, takes the
certificate, and feeds the observation to `RunState.step`. It prints one JSON
object: the next state and the certificate rows.
-/

open LeanMend LeanMend.Shell Lean

def baseline (target : System.FilePath) : IO UInt32 := do
  let toolchain := (← IO.FS.readFile (target / "lean-toolchain")).trimAscii.toString
  let mods ← moduleGraph target
  let order ← match topoOrder (mods.map (·.1)) with
    | .ok o => pure o
    | .error r => throw <| IO.userError s!"{repr r}"
  let st ← statuses target order
  let cert ← certificate target toolchain id mods st
  let failing := st.filterMap fun (n, s) => if s == .built then none else some n
  let next := (RunState.idle target.toString).step (.baseline cert failing)
  IO.println <| Json.compress <| Json.mkObj
    [("state", toJson next.tag), ("toolchain", toJson toolchain),
     ("order", toJson (order.map (·.name))), ("failing", toJson failing),
     ("decls", Json.arr (cert.decls.toArray.map fun d => Json.mkObj
        [("name", toJson d.name), ("module", toJson d.module),
         ("axioms", toJson d.axioms), ("statementHash", toJson d.statementHash)]))]
  return if failing.isEmpty then 0 else 1

/-- The summary of a finished run: the final state, the residue, and the
findings that wait for a card. -/
def summary (s : RunState) : Json :=
  let findings (fs : List Finding) := Json.arr (fs.toArray.map fun f => Json.mkObj
    [("decl", toJson f.decl.name), ("reason", toJson (toString (repr f.reason))),
     ("card", toJson ((f.reason.card.map fun k => toString (repr k)).getD "none"))])
  match s with
  | .done _ _ residue _ => Json.mkObj [("state", toJson s.tag), ("residue", toJson residue)]
  | .awaiting _ _ residue _ fs =>
    Json.mkObj [("state", toJson s.tag), ("residue", toJson residue), ("findings", findings fs)]
  | _ => Json.mkObj [("state", toJson s.tag)]

def runCmd (t : String) (rest : List String) : IO UInt32 := do
  let rec froms : List String → Option (List System.FilePath)
    | [] => some []
    | "--aliases-from" :: p :: more => (froms more).map (System.FilePath.mk p :: ·)
    | _ => none
  match rest with
  | "--adopt" :: more =>
    match froms more with
    | some ps =>
      let s ← runAdopt t ps
      IO.println (summary s).compress
      return match s with | .halted _ => 1 | _ => 0
    | none => IO.eprintln "usage: lean-mend run <target> --adopt [--aliases-from <project>]…"; return 2
  | _ => IO.eprintln "usage: lean-mend run <target> --adopt [--aliases-from <project>]…"; return 2

def main : List String → IO UInt32
  | ["baseline", t] => baseline t
  | "run" :: t :: rest => runCmd t rest
  | _ => do
    IO.eprintln "usage: lean-mend baseline <target> | lean-mend run <target> --adopt [--aliases-from <project>]…"
    return 2
