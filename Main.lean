import LeanMend
import LeanMend.Shell.Target

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
  let cert ← certificate target toolchain mods st
  let failing := st.filterMap fun (n, s) => if s == .built then none else some n
  let next := (RunState.idle target.toString).step (.baseline cert failing)
  IO.println <| Json.compress <| Json.mkObj
    [("state", toJson next.tag), ("toolchain", toJson toolchain),
     ("order", toJson (order.map (·.name))), ("failing", toJson failing),
     ("decls", Json.arr (cert.decls.toArray.map fun d => Json.mkObj
        [("name", toJson d.name), ("module", toJson d.module),
         ("axioms", toJson d.axioms), ("statementHash", toJson d.statementHash)]))]
  return if failing.isEmpty then 0 else 1

def main : List String → IO UInt32
  | ["baseline", t] => baseline t
  | _ => do IO.eprintln "usage: lean-mend baseline <target>"; return 2
