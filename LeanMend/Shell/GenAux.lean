import LeanMend.Core.GenAux
import LeanMend.Shell.Target
import LeanMend.Shell.DepDiff

/-!
# The generated-auxiliary diff, gathered (`docs/static-diff.md` § 3)

IO for `LeanMend.genAuxDiff`: run the probe's `export --ownClosure` at each
side's own toolchain, over every built module of the target
(`builtModuleNames`, the same set `dependencyRows` and `certificate` cover —
no person chooses which modules), parse the rows into `DepConst` (keeping
`uses`, which `LeanMend.Shell.parseExport` drops — `genAuxDiff` needs it to
walk which auxiliary a declaration's own compiled value actually reaches,
`LeanMend.Core.GenAux.reachableAux`'s doc comment), and compute the pure
diff.
-/

namespace LeanMend.Shell

open Lean (Json toJson)
open System (FilePath)

private def get {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"field '{k}': {e}"

/-- Parse one `export --ownClosure` run (`probe/Probe.lean`, `cmdExportOwnFull`)
into `DepConst`s: the same per-line shape `parseExport` reads, with `uses`
kept instead of dropped. -/
def parseOwnClosure (out : String) : Except String (List DepConst) := do
  let lines := (out.splitOn "\n" |>.filter (· ≠ ""))
  let mut consts : List DepConst := []
  for l in lines do
    let j ← Json.parse l
    if let .ok (n : String) := j.getObjValAs? String "const" then
      let bodyHash : Option String := (j.getObjValAs? String "body").toOption
      consts := consts ++ [{ name := n, module := ← get j "module", kind := ← get j "kind",
                              axioms := ← get j "axioms", bodyHash, uses := ← get j "uses" : DepConst }]
    else pure ()  -- `moduleFile`/`olean`/`sysroot` lines: not needed here (always the target).
  pure consts

/-- One `export --ownClosure` call, covering every built module of `root`
together (`docs/static-diff.md` § 3): the same clash-retry mechanism
`LeanMend.Shell.exportRows` already uses for two executable roots that
cannot share one `importModules` call (a genuine Lean limit, not specific
to this arm). One batched probe call per side for the whole step
(`docs/static-diff.md` § Cost rules), not one per module or declaration. -/
partial def ownClosureRows (root : FilePath) (toolchain : String) (all part : List String) :
    IO (List DepConst) := do
  if part.isEmpty then return []
  let rec go (cur moved : List String) : IO (String × List String) := do
    try
      let out ← probe root (#["export", "--ownClosure"] ++ cur.toArray ++ #["--"] ++ all.toArray)
      pure (out, moved)
    catch e =>
      let some x := clashModule e.toString | throw e
      unless cur.length > 1 && cur.contains x do throw e
      go (cur.filter (· != x)) (moved ++ [x])
  let (out, moved) ← go part []
  let consts ← parseOrThrow s!"probe export --ownClosure at {toolchain}" (parseOwnClosure out)
  if moved.isEmpty then return consts
  return consts ++ (← ownClosureRows root toolchain all moved)

/-- The target's own generated-auxiliary constants at one side: every
built module (`builtModuleNames`, the same set `certificate` and
`dependencyRows` cover), via `ownClosureRows`. -/
def ownConsts (root : FilePath) (toolchain : String) : IO (List DepConst) := do
  let names ← builtModuleNames root
  ownClosureRows root toolchain names names

/-- The generated-auxiliary diff of `base` against `after`
(`docs/static-diff.md` § 3): both sides' own-module constants
(`ownConsts`), then the pure diff (`LeanMend.genAuxDiff`). One probe call
per side, no caching: the probe already filters to each side's own
modules only, so the computation is bounded by the target's own size,
never the whole dependency set, and this phase runs once per bump
(`docs/static-diff.md` § 6), not repeatedly like the dependency diff a
second target pair could share. -/
def computeGenAuxDiff (base after : FilePath) : IO (List GenAuxEntry) := do
  let (baseToolchain, _) ← pinsOfRoot base
  let (afterToolchain, _) ← pinsOfRoot after
  let baseConsts ← ownConsts base baseToolchain
  let afterConsts ← ownConsts after afterToolchain
  pure (genAuxDiff baseConsts afterConsts)

/-! ## JSON, for the CLI -/

def auxRoleJson (r : AuxRole) : Json := toJson r.tag

def auxConstJson (c : AuxConst) : Json := Json.mkObj
  [("owner", toJson c.owner), ("role", auxRoleJson c.role),
   ("name", toJson c.const.name), ("module", toJson c.const.module), ("kind", toJson c.const.kind),
   ("axioms", toJson c.const.axioms),
   ("bodyHash", match c.const.bodyHash with | some b => toJson b | none => Json.null)]

def genAuxEntryJson (e : GenAuxEntry) : Json := Json.mkObj
  [("owner", toJson e.owner), ("role", auxRoleJson e.role), ("kind", kindJson e.kind),
   ("before", e.before.map auxConstJson |>.getD Json.null),
   ("after", e.after.map auxConstJson |>.getD Json.null)]

def genAuxPredictionJson (p : GenAuxPrediction) : Json := Json.mkObj
  [("owner", toJson p.owner), ("role", auxRoleJson p.role),
   ("axiomsAdded", toJson p.added), ("cause", toJson p.cause)]

end LeanMend.Shell
