import LeanMend.Core.Propagate
import LeanMend.Shell.DepDiff

/-!
# Propagation, gathered and run (`docs/static-diff.md` § 2)

IO for propagation (`LeanMend.Core.Propagate`): the stored dependency diff
(`LeanMend.Shell.computeDepDiff`, § 1, computed when absent), one batched
probe call over the target's own modules at each side (`export --own`,
`probe/Probe.lean`'s `cmdExportOwn`: the after side's graph and axiom
sets, and the base side's axiom sets, which `propagate` needs to tell a
genuinely new axiom reach from one the declaration already had), and the
pure `propagate` step over all three, with no further IO.
-/

namespace LeanMend.Shell

open Lean (Json toJson)
open System (FilePath)

private def get {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"field '{k}': {e}"

/-! ## Gathering one side's own graph -/

/-- Parse one `export --own` run (`probe/Probe.lean`, `cmdExportOwn`) into
`DepConst`s: every line but the trailing `{"sysroot"}` line is one own
constant. -/
def parseOwn (out : String) : Except String (List DepConst) := do
  let lines := (out.splitOn "\n" |>.filter (· ≠ ""))
  let mut out : List DepConst := []
  for l in lines do
    let j ← Json.parse l
    if let .ok (n : String) := j.getObjValAs? String "const" then
      out := out ++ [{ name := n, module := ← get j "module", kind := ← get j "kind",
                        uses := ← get j "uses", axioms := ← get j "axioms", bodyHash := none : DepConst }]
    else pure ()
  pure out

/-- Every built module of `root` (`own`, from `moduleGraph`), and the
`export --own` rows of all of them together: the clash recovery
`LeanMend.Shell.DepDiff.exportRows` already uses for two independently-
built executable roots (`docs/static-diff.md` § 1, decision S2) — on the
clash Lean reports, drop the named module from the call and retry, run
every module dropped this way in its own later call, seeded from and
excluded by the same, full own-module list every call uses, and take the
union of every call's rows, by name. -/
partial def ownRows (root : FilePath) (all part : List String) : IO (List DepConst) := do
  if part.isEmpty then return []
  let rec go (cur moved : List String) : IO (String × List String) := do
    try
      let out ← probe root (#["export", "--own"] ++ cur.toArray ++ #["--"] ++ all.toArray)
      pure (out, moved)
    catch e =>
      let some x := clashModule e.toString | throw e
      unless cur.length > 1 && cur.contains x do throw e
      go (cur.filter (· != x)) (moved ++ [x])
  let (out, moved) ← go part []
  let rows ← parseOrThrow s!"probe export --own at {root}" (parseOwn out)
  if moved.isEmpty then return rows
  return rows ++ (← ownRows root all moved)

/-- One side's own-declaration graph (`docs/static-diff.md` § 2): one
batched probe call (or more, on a clash) over every built module of
`root`, the same own-module list `computeDepDiff` already reads
(`builtModuleNames`), so propagation's graph and the dependency diff it
walks agree on which declarations are the target's own. -/
def ownGraph (root : FilePath) : IO (List DepConst) := do
  let names ← builtModuleNames root
  ownRows root names names

/-- One side's own declarations' axiom sets, by name (`ownGraph`'s own
`axioms` field) — the shape `propagate`'s `baseAxioms` needs. -/
def ownAxioms (root : FilePath) : IO (Std.HashMap String (List String)) := do
  let own ← ownGraph root
  pure (own.foldl (fun m c => m.insert c.name c.axioms) {})

/-! ## JSON of a prediction -/

def axiomPredictionJson (p : AxiomPrediction) : Json := Json.mkObj
  [("decl", toJson p.decl), ("module", toJson p.module),
   ("axiomsAdded", toJson p.axiomsAdded), ("axiomsRemoved", toJson p.axiomsRemoved),
   ("cause", toJson p.cause), ("causeModule", toJson p.causeModule), ("path", toJson p.path)]

def behaviorPredictionJson (p : BehaviorPrediction) : Json := Json.mkObj
  [("decl", toJson p.decl), ("module", toJson p.module),
   ("cause", toJson p.cause), ("causeModule", toJson p.causeModule), ("path", toJson p.path)]

def predictionsJson (p : Predictions) : Json := Json.mkObj
  [("axioms", Json.arr (p.axioms.toArray.map axiomPredictionJson)),
   ("behavior", Json.arr (p.behavior.toArray.map behaviorPredictionJson))]

/-! ## The run -/

/-- Propagation (`docs/static-diff.md` § 2): the dependency diff of `base`
against `after` (`computeDepDiff`, read from its cache when the pins and
the built-module lists match, computed otherwise), the after side's own
graph (`ownGraph after`), the base side's own axiom sets (`ownAxioms
base`), and the pure `propagate` step over all three. The second element
of the result is whether the dependency diff came from the cache. -/
def computePropagation (base after : FilePath) (cacheDir : Option FilePath := none) :
    IO (Predictions × Bool) := do
  let (entries, cached, _) ← computeDepDiff base after cacheDir
  let own ← ownGraph after
  let baseAxioms ← ownAxioms base
  pure (propagate entries own baseAxioms, cached)

end LeanMend.Shell
