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
  let (order, st) ← buildAll target [] order
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

structure RunOpts where
  targets : List String := []
  aliasesFrom : List System.FilePath := []
  prepare : List String := []
  rules : Option System.FilePath := none
  annotate : Bool := false
  follow : Bool := false
  speculate : Nat := defaultSpeculate

def usage : String :=
  "usage: lean-mend baseline <target>\n" ++
  "       lean-mend run <target> --adopt [--targets <t,…>] [--prepare <cmd>]\n" ++
  "                 [--rules <dir>] [--annotate-binders]\n" ++
  "                 [--follow-definition-changes] [--speculate <n>]\n" ++
  "                 [--aliases-from <project>]…\n" ++
  "       lean-mend cards <target>\n" ++
  "       lean-mend judge <target> <card> accept|reject --by <name>"

def parseOpts : List String → Option RunOpts
  | [] => some {}
  | "--aliases-from" :: p :: more => (parseOpts more).map fun o => { o with aliasesFrom := p :: o.aliasesFrom }
  | "--targets" :: ts :: more => (parseOpts more).map fun o => { o with targets := ts.splitOn "," ++ o.targets }
  | "--prepare" :: cmd :: more => (parseOpts more).map fun o => { o with prepare := (cmd.splitOn " ").filter (· ≠ "") }
  | "--rules" :: d :: more => (parseOpts more).map fun o => { o with rules := some d }
  | "--annotate-binders" :: more => (parseOpts more).map fun o => { o with annotate := true }
  | "--follow-definition-changes" :: more => (parseOpts more).map fun o => { o with follow := true }
  | "--speculate" :: n :: more => n.toNat?.bind fun w => (parseOpts more).map fun o => { o with speculate := w }
  | _ => none

/-- Every `*.json` file of a rules directory, in file-name order, parsed. A file
that does not parse stops the run (`docs/rules.md`). -/
def loadRules (dir : System.FilePath) : IO (List Rule) := do
  let files := ((← dir.readDir).map (·.path)).filter (·.extension == some "json")
  let sorted := files.qsort (·.toString < ·.toString)
  sorted.toList.mapM fun f => do
    let txt ← IO.FS.readFile f
    match Json.parse txt >>= Parse.rule with
    | .ok r => pure r
    | .error e => throw <| IO.userError s!"rule file {f}: {e}"

def runCmd (t : String) (rest : List String) : IO UInt32 := do
  match rest with
  | "--adopt" :: more =>
    match parseOpts more with
    | some o =>
      let rules ← match o.rules with
        | some d => loadRules d
        | none => pure []
      let s ← runAdopt t o.targets o.aliasesFrom o.prepare rules o.annotate o.follow o.speculate
      let target ← IO.FS.realPath t
      let ws ← ledgerWarnings (target / ".lean-mend" / "ledger.jsonl")
      IO.println ((summary s).setObjVal! "warnings" (toJson ws)).compress
      return match s with | .halted _ => 1 | _ => 0
    | none => IO.eprintln usage; return 2
  | _ => IO.eprintln usage; return 2

def main : List String → IO UInt32
  | ["baseline", t] => baseline t
  | "run" :: t :: rest => runCmd t rest
  | ["cards", t] => do
    for c in ← openCards t do
      IO.println s!"{c.id} {cardKindName c.kind} {c.subject}  ({t}/.lean-mend/cards/{c.id}.md)"
    return 0
  | ["judge", t, card, ans, "--by", who] => do
    let answer ← match ans with
      | "accept" => pure Answer.accept
      | "reject" => pure Answer.reject
      | _ => do IO.eprintln usage; return 2
    let s ← judge t card answer who
    IO.println (summary s).compress
    return match s with | .halted _ => 1 | _ => 0
  | _ => do IO.eprintln usage; return 2
