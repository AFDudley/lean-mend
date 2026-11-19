import LeanMend
import LeanMend.Shell.Target
import LeanMend.Shell.Driver
import LeanMend.Shell.DepDiff
import LeanMend.Shell.Propagate
import LeanMend.Shell.GenAux

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
  let cert ← match ← certificate target toolchain id mods st with
    | .ok cert => pure cert
    | .error x => throw <| IO.userError x.message
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
  /-- `--max-memory <GiB>` (`docs/parallel.md` P24). -/
  maxMemory : Option Nat := none
  /-- `--probe-cap <MiB>`: the hard cap of each probe (`docs/parallel.md` P24). -/
  probeCap : Option Nat := none

def usage : String :=
  "usage: lean-mend baseline <target>\n" ++
  "       lean-mend run <target> --adopt [--targets <t,…>] [--prepare <cmd>]\n" ++
  "                 [--rules <dir>] [--annotate-binders]\n" ++
  "                 [--follow-definition-changes] [--speculate <n>]\n" ++
  "                 [--max-memory <GiB>] [--probe-cap <MiB>]\n" ++
  "                 [--aliases-from <project>]…\n" ++
  "       lean-mend cards <target>\n" ++
  "       lean-mend dep-diff <base> <after> [--cache <dir>]\n" ++
  "       lean-mend comp-eq <base> <after> <decl>…\n" ++
  "       lean-mend propagate <base> <after> [--cache <dir>]\n" ++
  "       lean-mend gen-aux <base> <after>\n" ++
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
  | "--max-memory" :: n :: more => n.toNat?.bind fun g => (parseOpts more).map fun o => { o with maxMemory := some g }
  | "--probe-cap" :: n :: more => n.toNat?.bind fun m => (parseOpts more).map fun o => { o with probeCap := some m }
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

/-- `dep-diff <base> <after>` (`docs/static-diff.md` § 1, decision S2): the
dependency diff of two built trees of the same target at two pins, each at
its own toolchain (`computeDepDiff`, every built module of the target —
no root choice). One JSON object: `cached` (whether the pins' store
already held the result), `cacheFile` (where it is now), and `entries`
(`depDiffEntryJson`). -/
def depDiffCmd (base after : System.FilePath) (cacheDir : Option System.FilePath) : IO UInt32 := do
  let (es, cached, file) ← computeDepDiff base after cacheDir
  IO.println <| Json.compress <| Json.mkObj
    [("cached", toJson cached), ("cacheFile", toJson file.toString),
     ("entries", Json.arr (es.toArray.map depDiffEntryJson))]
  return 0

/-- `comp-eq <base> <after> <decl>…` (`docs/static-diff.md` § 4,
computational equality): `LeanMend.Shell.certifyBehaviors` on the named
declarations directly, with no certificate and no run — a standalone
entry point to measure and check the mechanism against a real target's
two built trees, the same way `dep-diff` stands alone from a run. One
JSON array, one object per declaration: `{"decl", "result"}`, `result` a
`{"tag": "certified", "trustPoints"}` or a `{"tag": "differsAt",
"constant", "reason"}`. -/
def compEqCmd (base after : System.FilePath) (declNames : List String) : IO UInt32 := do
  let head (dir : System.FilePath) : IO String := do
    pure ((← git dir #["rev-parse", "HEAD"]).splitOn "\n").head!
  let baseToolchain := (← IO.FS.readFile (base / "lean-toolchain")).trimAscii.toString
  let afterToolchain := (← IO.FS.readFile (after / "lean-toolchain")).trimAscii.toString
  let baseTree : Tree :=
    { dir := base, toolchain := baseToolchain, files := [], commit := ← head base,
      probe := probe base, request := base / ".lean-mend" / "comp-eq.json" }
  let afterTree : Tree :=
    { dir := after, toolchain := afterToolchain, files := [], commit := ← head after,
      probe := probe after, request := after / ".lean-mend" / "comp-eq.json" }
  let dummyDecl (n : String) : Decl :=
    { name := n, module := "", kind := .other, statementHash := "", bodyHash := "", axioms := [] }
  let fs : List Finding := declNames.map fun n => { decl := dummyDecl n, reason := .definitionChanged }
  let results ← certifyBehaviors (Names.ofAliases { pairs := [] }) baseTree afterTree fs fs
  IO.println <| Json.compress <| Json.arr (results.toArray.map fun (n, r) => Json.mkObj
    [("decl", toJson n), ("result", match r with
       | .certified tps => Json.mkObj [("tag", toJson "certified"),
           ("trustPoints", Json.arr (tps.toArray.map fun t => Json.mkObj
              [("name", toJson t.name), ("kind", toJson t.kind)]))]
       | .differsAt c reason => Json.mkObj
           [("tag", toJson "differsAt"), ("constant", toJson c), ("reason", toJson reason)])])
  return 0

/-- `propagate <base> <after>` (`docs/static-diff.md` § 2): the predicted
findings of the dependency diff of `base` against `after`
(`computeDepDiff`, computed when its cache has no entry for the pins),
through the after side's own-declaration graph (`ownGraph`, one batched
probe call, `export --own`). One JSON object: `cached` (whether the
dependency diff came from its own cache), `axioms` and `behavior`
(`predictionsJson`). -/
def propagateCmd (base after : System.FilePath) (cacheDir : Option System.FilePath) :
    IO UInt32 := do
  let (preds, cached) ← computePropagation base after cacheDir
  IO.println <| Json.compress <|
    (predictionsJson preds).mergeObj (Json.mkObj [("cached", toJson cached)])
  return 0

/-- `gen-aux <base> <after>` (`docs/static-diff.md` § 3): the
generated-auxiliary diff of two built trees of the same target at two
pins, each at its own toolchain (`computeGenAuxDiff`, every built module
of the target). One JSON object: `entries` (`genAuxEntryJson`) and
`predictions` (`genAuxPredictionJson`, `predictionsOf` — the entries that
predict a Violation, cause named). -/
def genAuxCmd (base after : System.FilePath) : IO UInt32 := do
  let es ← computeGenAuxDiff base after
  IO.println <| Json.compress <| Json.mkObj
    [("entries", Json.arr (es.toArray.map genAuxEntryJson)),
     ("predictions", Json.arr ((predictionsOf es).toArray.map genAuxPredictionJson))]
  return 0

def runCmd (t : String) (rest : List String) : IO UInt32 := do
  match rest with
  | "--adopt" :: more =>
    match parseOpts more with
    | some o =>
      let rules ← match o.rules with
        | some d => loadRules d
        | none => pure []
      let r ← runAdopt t o.targets o.aliasesFrom o.prepare rules o.annotate o.follow o.speculate
        o.maxMemory o.probeCap
      match r with
      | .error x =>
        -- A typed stop: a probe passed its hard cap (`docs/parallel.md`
        -- P24), or the certificate has no row for a declaration
        -- (`docs/verification.md` § The certificate). Exit 3.
        IO.eprintln x.message
        let (name, fields) := x.note
        IO.println <| Json.compress <| Json.mkObj
          ([("state", toJson s!"halted {name}")] ++ fields)
        return 3
      | .ok s =>
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
  | "dep-diff" :: base :: after :: rest =>
    match rest with
    | [] => depDiffCmd base after none
    | ["--cache", d] => depDiffCmd base after (some d)
    | _ => do IO.eprintln usage; return 2
  | "comp-eq" :: base :: after :: decls => compEqCmd base after decls
  | "propagate" :: base :: after :: rest =>
    match rest with
    | [] => propagateCmd base after none
    | ["--cache", d] => propagateCmd base after (some d)
    | _ => do IO.eprintln usage; return 2
  | "gen-aux" :: base :: after :: [] => genAuxCmd base after
  | ["judge", t, card, ans, "--by", who] => do
    let answer ← match ans with
      | "accept" => pure Answer.accept
      | "reject" => pure Answer.reject
      | _ => do IO.eprintln usage; return 2
    let s ← judge t card answer who
    IO.println (summary s).compress
    return match s with | .halted _ => 1 | _ => 0
  | _ => do IO.eprintln usage; return 2
