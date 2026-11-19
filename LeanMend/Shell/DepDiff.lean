import LeanMend.Core.DepDiff
import LeanMend.Shell.Target
import LeanMend.Shell.Cause

/-!
# The dependency diff, gathered and cached (`docs/static-diff.md` § 1)

IO for the dependency diff (`LeanMend.Core.DepDiff`, decision S2): run the
probe's `export` command at each side's own toolchain over its own modules
plus everything they import (Lean core, Std, Batteries, Mathlib and any
other package), drop the rows that belong to the target's own modules
(`moduleGraph`), resolve each remaining row's owner the way card-cause does
(`LeanMend.Shell.Cause.ownerOfOlean`), and compute the pure diff
(`LeanMend.depDiff`).

## Storage

The diff does not depend on the target, only on the pair of pins (decision
S2): the two toolchains, and the two `lake-manifest.json` package
revisions. A second call with the same pins must read the stored result,
not export again — a full Mathlib export measures tens of minutes
(`docs/static-diff.md` § Cost, `tests/dep-diff-cache.sh`). The key is
`toString (hash (pinsCanonical p))`: the two toolchains and every package's
`(name, rev)` pair of both manifests, sorted by package name and joined
into one string, hashed the same way `Shell.Target.probeStamp` keys the
compiled probe (`hash` on a canonical string, not a cryptographic digest —
collisions are theoretically possible but excluded in practice by the same
margin a build stamp already relies on). The file lives at
`<after>/.lean-mend/dep-diff/<key>.json`, next to the target's other
`.lean-mend` state (`session.json`, `cards/`): one pair of pins can serve
more than one target that bumps between them, but each target's own tree is
where lean-mend already keeps its state, and `--cache <dir>` overrides the
location for a caller that wants one store shared across targets.
-/

namespace LeanMend.Shell

open Lean (Json toJson)
open System (FilePath)

private def get {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"field '{k}': {e}"

/-! ## Gathering one side -/

/-- The owner of a dependency module, from the `.olean` file the toolchain
loads it from: Lean core under the toolchain's own root, else the package
under `.lake/packages/<p>/` at its manifest `rev` (a path package with no
`rev` falls back the way `manifestRevs` already does). The shell filters
out the target's own modules before this runs (`parseExport`), so those are
the only two cases a dependency module's olean can be in; an olean in
neither is reported, not silently dropped. Mirrors
`LeanMend.Shell.Cause.ownerOfOlean`'s first two cases; that function's
third case (the target itself) cannot apply to a dependency row. -/
def depOwnerOfOlean (sysroot toolchain : String)
    (manifest : Option (String × List (String × String))) (olean : String) : Owner :=
  if olean.startsWith sysroot then ⟨"Lean core", toolchain⟩ else
  let parts := olean.splitOn "/.lake/packages/"
  if parts.length > 1 then
    let p := ((parts.getLast!).splitOn "/").head!
    match manifest with
    | some (_, revs) => ⟨p, (revs.lookup p).getD "not in lake-manifest.json"⟩
    | none => ⟨p, "no lake-manifest.json"⟩
  else ⟨"unknown", s!"olean outside sysroot and .lake/packages: {olean}"⟩

/-- Parse one `export --closure` run (`probe/Probe.lean`, `cmdExport`)
into `DepRow`s, keeping only the constants whose module is not in `own`
(the target's own modules, from `moduleGraph`): the dependency modules
(`docs/static-diff.md` § 1). `export --closure`'s `body` field is a hash
string (`null` for a constant with no value), already the comparable form
`DepDiff.depDiff` equates. -/
def parseExport (toolchain : String) (manifest : Option (String × List (String × String)))
    (own : Std.HashSet String) (out : String) : Except String (List DepRow) := do
  let lines := (out.splitOn "\n" |>.filter (· ≠ ""))
  let mut consts : List DepConst := []
  let mut oleans : List (String × String) := []
  let mut sysroot : Option String := none
  for l in lines do
    let j ← Json.parse l
    if let .ok (n : String) := j.getObjValAs? String "const" then
      let m : String ← get j "module"
      unless own.contains m do
        let bodyHash : Option String := (j.getObjValAs? String "body").toOption
        consts := consts ++ [{ name := n, module := m, kind := ← get j "kind",
                                axioms := ← get j "axioms", uses := ← get j "uses",
                                bodyHash : DepConst }]
    else if let .ok (m : String) := j.getObjValAs? String "moduleFile" then
      oleans := oleans ++ [(m, ← get j "olean")]
    else if let .ok (s : String) := j.getObjValAs? String "sysroot" then sysroot := some s
    else pure ()
  let some sys := sysroot | throw "export: no sysroot line"
  let owners := oleans.foldl (init := ({} : Std.HashMap String Owner)) fun m (mo, ol) =>
    m.insert mo (depOwnerOfOlean sys toolchain manifest ol)
  pure (consts.map fun c =>
    { const := c, owner := (owners[c.module]?).getD ⟨"unknown", s!"no olean line for {c.module}"⟩ })

/-- One side's dependency rows: one or more `export --closure` calls
(`docs/static-diff.md` § 1, decision S2), together covering every built
module of `root` (`moduleGraph`; `Shell.Target.certificate` covers the
same set) — no person chooses which modules to include.

Two independently-built executable roots that each declare their own
`main` cannot be in the same `importModules` call (a genuine Lean
limit). `exportRows` recovers the way `Shell.Target.declsOf` already
does for the certificate: on the clash Lean reports, drop the named
module from this call (`clashModule`) and retry; every module dropped
this way runs in its own later call, seeded from and excluded by the
same, full own-module list (`all`) every call uses, so a module in one
call's own declarations is never misread as a dependency because
another call happened to import it. The union of every call's rows,
by name, is the result — a clash costs one extra probe call per
colliding module, never a missing one. -/
partial def exportRows (root : FilePath) (toolchain : String)
    (manifest : Option (String × List (String × String))) (ownNames : Std.HashSet String)
    (all part : List String) : IO (List DepRow) := do
  if part.isEmpty then return []
  let rec go (cur moved : List String) : IO (String × List String) := do
    try
      let out ← probe root (#["export", "--closure"] ++ cur.toArray ++ #["--"] ++ all.toArray)
      pure (out, moved)
    catch e =>
      let some x := clashModule e.toString | throw e
      unless cur.length > 1 && cur.contains x do throw e
      go (cur.filter (· != x)) (moved ++ [x])
  let (out, moved) ← go part []
  let rows ← parseOrThrow s!"probe export at {toolchain}" (parseExport toolchain manifest ownNames out)
  if moved.isEmpty then return rows
  return rows ++ (← exportRows root toolchain manifest ownNames all moved)

/-- Every built module of `root` (`moduleGraph`; an unbuilt module, for
example a test file outside its default targets, is not a root — the
probe cannot import an `.olean` that does not exist), and the dependency
rows of all of them together (`exportRows`). -/
def dependencyRows (root : FilePath) (toolchain : String)
    (manifest : Option (String × List (String × String))) : IO (List DepRow) := do
  let own ← moduleGraph root
  let ownNames : Std.HashSet String := own.foldl (init := ({} : Std.HashSet String))
    fun s (m, _) => s.insert m.name
  let oleanOf (f : FilePath) : FilePath := root / ".lake" / "build" / "lib" / "lean" / f.withExtension "olean"
  let built ← own.filterM fun (_, f) => (oleanOf f).pathExists
  let names := built.map (·.1.name)
  exportRows root toolchain manifest ownNames names names

/-- Every built module of `root`, by name (`dependencyRows`'s own list,
exposed so `computeDepDiff` can read it for the cache key without a
probe run). -/
def builtModuleNames (root : FilePath) : IO (List String) := do
  let own ← moduleGraph root
  let oleanOf (f : FilePath) : FilePath := root / ".lake" / "build" / "lib" / "lean" / f.withExtension "olean"
  pure ((← own.filterM fun (_, f) => (oleanOf f).pathExists).map (·.1.name))

/-! ## The pair of pins, as a cache key -/

/-- The toolchain and the `lake-manifest.json` package revisions of one
root (`docs/decisions.md` D15's `manifestRevs`, reused here for the pins
key, not for an owner lookup). -/
def pinsOfRoot (root : FilePath) : IO (String × List (String × String)) := do
  let toolchain := (← IO.FS.readFile (root / "lean-toolchain")).trimAscii.toString
  let revs := ((← manifestRevs root).map (·.2)).getD []
  pure (toolchain, revs)

/-- The pair of pins a dependency diff is keyed by: both toolchains, both
`lake-manifest.json`s, each side's own-module list (`builtModuleNames`,
§ Storage) and each side's built content (`builtContentHash`). A target
whose own module list changes between two calls on the same toolchains and
manifests (a new file, for example, carrying a new import) is a different
closure walk and so a different result; a rebuild that changes a built
file is a different input. Neither may read a cache entry of the old one. -/
structure Pins where
  baseToolchain : String
  baseRevs : List (String × String)
  afterToolchain : String
  afterRevs : List (String × String)
  baseModules : List String
  afterModules : List String
  baseBuild : String
  afterBuild : String
  deriving Repr

/-- `Pins`, as one string, package revisions and module lists sorted so
the same pins always canonicalize the same way regardless of order. -/
def pinsCanonical (p : Pins) : String :=
  let revStr (rs : List (String × String)) :=
    "\n".intercalate ((rs.toArray.qsort (fun a b => a.1 < b.1)).toList.map fun (k, v) => s!"{k}={v}")
  let sortedStr (xs : List String) := "\n".intercalate (xs.toArray.qsort (· < ·)).toList
  s!"{p.baseToolchain}\n{revStr p.baseRevs}\n--\n{p.afterToolchain}\n{revStr p.afterRevs}\n--\n{sortedStr p.baseModules}\n--\n{sortedStr p.afterModules}\n--\n{p.baseBuild}\n{p.afterBuild}"

/-- The cache key of `p` (§ Storage): `hash` of the canonical form, the same
way `Shell.Target.probeStamp` keys the compiled probe. -/
def pinsKey (p : Pins) : String := toString (hash (pinsCanonical p))

def revsJson (rs : List (String × String)) : Json :=
  Json.arr (rs.toArray.map fun (p, r) => toJson [p, r])

def pinsJson (p : Pins) : Json := Json.mkObj
  [("baseToolchain", toJson p.baseToolchain), ("baseRevs", revsJson p.baseRevs),
   ("afterToolchain", toJson p.afterToolchain), ("afterRevs", revsJson p.afterRevs),
   ("baseModules", toJson p.baseModules), ("afterModules", toJson p.afterModules),
   ("baseBuild", toJson p.baseBuild), ("afterBuild", toJson p.afterBuild)]

/-! ## JSON of a dependency diff, for the cache file -/

def ownerJson (o : Owner) : Json := toJson [o.package, o.rev]

def ownerOf (j : Json) : Except String Owner := do
  let l : List String ← get j "owner"
  match l with
  | [p, r] => pure ⟨p, r⟩
  | _ => throw "evidence: an owner is not [package, rev]"


def depConstJson (c : DepConst) : Json := Json.mkObj
  [("name", toJson c.name), ("module", toJson c.module), ("kind", toJson c.kind),
   ("axioms", toJson c.axioms), ("uses", toJson c.uses),
   ("bodyHash", match c.bodyHash with | some b => toJson b | none => Json.null)]

/-- `uses` is read tolerantly (`[]` when absent): a cache file written
before this field existed still parses, with no further-chain
continuation past such a row (`docs/static-diff.md` § 2's
`deepestChange`). -/
def depConstOf (j : Json) : Except String DepConst := do
  let bodyHash : Option String := (j.getObjValAs? String "bodyHash").toOption
  let uses : List String := (j.getObjValAs? (List String) "uses").toOption.getD []
  pure { name := ← get j "name", module := ← get j "module", kind := ← get j "kind",
         axioms := ← get j "axioms", uses, bodyHash }

def depRowJson (r : DepRow) : Json :=
  (depConstJson r.const).mergeObj (Json.mkObj [("owner", ownerJson r.owner)])

def depRowOf (j : Json) : Except String DepRow := do
  pure { const := ← depConstOf j, owner := ← ownerOf j }

def kindJson : DepDiffKind → Json
  | .axioms added removed => Json.mkObj
      [("tag", toJson "axioms"), ("axiomsAdded", toJson added), ("axiomsRemoved", toJson removed)]
  | .body => Json.mkObj [("tag", toJson "body")]
  | .onlyBefore => Json.mkObj [("tag", toJson "onlyBefore")]
  | .onlyAfter => Json.mkObj [("tag", toJson "onlyAfter")]

def kindOf (j : Json) : Except String DepDiffKind := do
  match (← get j "tag" : String) with
  | "axioms" => pure (.axioms (← get j "axiomsAdded") (← get j "axiomsRemoved"))
  | "body" => pure .body
  | "onlyBefore" => pure .onlyBefore
  | "onlyAfter" => pure .onlyAfter
  | t => throw s!"unknown dependency-diff kind '{t}'"

def depDiffEntryJson (e : DepDiffEntry) : Json := Json.mkObj
  [("name", toJson e.name), ("kind", kindJson e.kind),
   ("before", e.before.map depRowJson |>.getD Json.null),
   ("after", e.after.map depRowJson |>.getD Json.null)]

def depDiffEntryOf (j : Json) : Except String DepDiffEntry := do
  let before ← match j.getObjValD "before" with
    | Json.null => pure none
    | b => some <$> depRowOf b
  let after ← match j.getObjValD "after" with
    | Json.null => pure none
    | a => some <$> depRowOf a
  pure { name := ← get j "name", kind := ← kindOf (← get (α := Json) j "kind"), before, after }

def resultJson (p : Pins) (es : List DepDiffEntry) : Json := Json.mkObj
  [("pins", pinsJson p), ("entries", Json.arr (es.toArray.map depDiffEntryJson))]

def resultOf (j : Json) : Except String (List DepDiffEntry) := do
  let es : List Json ← get j "entries"
  es.mapM depDiffEntryOf

/-! ## The cached, pin-keyed diff -/

/-- `<after>/.lean-mend/dep-diff` (§ Storage). -/
def defaultCacheDir (after : FilePath) : FilePath := after / ".lean-mend" / "dep-diff"

/-- The dependency diff of `base` against `after` (decision S2): the pins'
cache file in `cacheDir` (`defaultCacheDir after` when `cacheDir` is
`none`), read when it exists, else both sides' `export` runs
(`dependencyRows`, every built module of each side), the diff, and a
write of the file before returning. The second element is whether the
result came from the cache. The cache key reads each side's built-module
list (`builtModuleNames`) and built content (`builtContentHash`) before
the cache check, with no probe run: a changed module list or a rebuilt
file misses the cache instead of reading a result of the old input
(§ Storage, law LM3). -/
def computeDepDiff (base after : FilePath) (cacheDir : Option FilePath := none) :
    IO (List DepDiffEntry × Bool × FilePath) := do
  let (baseToolchain, baseRevs) ← pinsOfRoot base
  let (afterToolchain, afterRevs) ← pinsOfRoot after
  let baseModules ← builtModuleNames base
  let afterModules ← builtModuleNames after
  let baseBuild ← builtContentHash base
  let afterBuild ← builtContentHash after
  let pins : Pins := { baseToolchain, baseRevs, afterToolchain, afterRevs,
                        baseModules, afterModules, baseBuild, afterBuild }
  let dir := cacheDir.getD (defaultCacheDir after)
  let file := dir / s!"{pinsKey pins}.json"
  if ← file.pathExists then
    let es ← parseOrThrow s!"dep-diff cache {file}" (Json.parse (← IO.FS.readFile file) >>= resultOf)
    pure (es, true, file)
  else
    let baseManifest ← manifestRevs base
    let afterManifest ← manifestRevs after
    let baseRows ← dependencyRows base baseToolchain baseManifest
    let afterRows ← dependencyRows after afterToolchain afterManifest
    let es := depDiff baseRows afterRows
    IO.FS.createDirAll dir
    IO.FS.writeFile file (resultJson pins es).compress
    pure (es, false, file)

end LeanMend.Shell
