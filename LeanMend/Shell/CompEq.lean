import LeanMend.Core.CompEq
import LeanMend.Shell.DepDiff
import LeanMend.Shell.Cause

/-!
# Computational equality, gathered (`docs/static-diff.md` § 4)

IO for `LeanMend.certifyEqual` (`LeanMend.Core.CompEq`): the probe's new
`terms` command, at each side, batched once per side for the whole round
(the cost rule "one probe process per side for a whole slice step, not one
per declaration", `.scratch/static-diff-review.md`); the dependency diff
(`LeanMend.Shell.DepDiff.computeDepDiff`, already cached per pair of pins);
and each constant's status (`LeanMend.ConstStatus`), from the open findings
of this run and the dependency diff's entries. JSON stays in the shell
(concept B2); `LeanMend.Shell.Driver.autoAcceptCompEq` wires the result into
`certify`.
-/

namespace LeanMend.Shell

open Lean (Json toJson)
open System (FilePath)

private def get {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"field '{k}': {e}"

/-- Parse `erasedBody`'s JSON shape (`probe/Probe.lean`) into `ErasedTerm`:
the inverse of `erasedBody`, one case per constructor it emits. -/
partial def erasedTermOf (j : Json) : Except String ErasedTerm :=
  match j with
  | Json.str "#" => pure .erased
  | Json.str "?fvar" => pure .erased
  | Json.str "?mvar" => pure .erased
  | _ =>
    if let .ok (i : Nat) := j.getObjValAs? Nat "bvar" then pure (.bvar i)
    else if let .ok (lvl : String) := j.getObjValAs? String "sort" then pure (.sort lvl)
    else if let .ok (n : String) := j.getObjValAs? String "const" then do
      let us ← get j "us"
      pure (.const n us)
    else if let .ok (av : Json) := j.getObjVal? "app" then
      match av with
      | Json.arr arr =>
        match arr[0]?, arr[1]? with
        | some f, some a => do pure (.app (← erasedTermOf f) (← erasedTermOf a))
        | _, _ => throw "terms: 'app' array has fewer than 2 elements"
      | _ => throw "terms: 'app' is not an array"
    else if let .ok (l : Json) := j.getObjVal? "lam" then do
      let bi : String ← get l "bi"
      let ty ← l.getObjVal? "ty"
      let body ← l.getObjVal? "body"
      pure (.lam bi (← erasedTermOf ty) (← erasedTermOf body))
    else if let .ok (l : Json) := j.getObjVal? "forallE" then do
      let bi : String ← get l "bi"
      let ty ← l.getObjVal? "ty"
      let body ← l.getObjVal? "body"
      pure (.forallE bi (← erasedTermOf ty) (← erasedTermOf body))
    else if let .ok (l : Json) := j.getObjVal? "letE" then do
      let ty ← l.getObjVal? "ty"
      let val ← l.getObjVal? "val"
      let body ← l.getObjVal? "body"
      pure (.letE (← erasedTermOf ty) (← erasedTermOf val) (← erasedTermOf body))
    else if let .ok (n : String) := j.getObjValAs? String "nat" then pure (.nat n)
    else if let .ok (s : String) := j.getObjValAs? String "str" then pure (.str s)
    else if let .ok (p : Json) := j.getObjVal? "proj" then do
      let ty : String ← get p "type"
      let idx : Nat ← get p "idx"
      let s ← p.getObjVal? "struct"
      pure (.proj ty idx (← erasedTermOf s))
    else throw s!"terms: unrecognized erased-body shape: {j.compress}"

/-- One constant of a `terms` call (`probe/Probe.lean`, `cmdTerms`): its
module, kind, whether it is a stated trust point (decision S4), and its
full erased body (`none` for a constant with no value). -/
structure TermRow where
  name : String
  module : String
  kind : String
  trust : Option String
  body : Option ErasedTerm
  /-- The constant's equations, erased, when it has usable ones
  (`probe/Probe.lean`, `eqnsOfConst`; decision S8). -/
  eqns : Option (List Equation)
  deriving Repr

/-- One `terms` run's own data: the rows the closure reached, the roots the
environment does not hold, the modules touched (for an owner lookup, not
needed here since `terms` already tells apart owned and dependency
constants by `ownMods`), and the sysroot. -/
structure TermsOut where
  rows : List TermRow
  missing : List String
  deriving Repr

def parseTerms (out : String) : Except String TermsOut := do
  let lines := (out.splitOn "\n" |>.filter (· ≠ ""))
  let mut rows : List TermRow := []
  let mut missing : List String := []
  for l in lines do
    let j ← Json.parse l
    if let .ok (n : String) := j.getObjValAs? String "const" then
      let kind : String ← get j "kind"
      let trust : Option String := (j.getObjValAs? String "trust").toOption
      let body ← match j.getObjValD "body" with
        | Json.null => pure none
        | b => some <$> erasedTermOf b
      let eqns ← match j.getObjValD "eqns" with
        | Json.null => pure none
        | Json.arr es => some <$> es.toList.mapM fun e => do
            pure { binders := ← get e "binders", lhs := ← erasedTermOf (← e.getObjVal? "lhs"),
                   rhs := ← erasedTermOf (← e.getObjVal? "rhs") : Equation }
        | _ => throw "terms: 'eqns' is not an array"
      rows := rows ++ [{ name := n, module := ← get j "module", kind, trust, body, eqns : TermRow }]
    else if let .ok (n : String) := j.getObjValAs? String "missing" then missing := missing ++ [n]
    else pure ()  -- `moduleFile`/`olean`/`sysroot`: not needed, `ownMods` already tells owned from dependency.
  pure { rows, missing }

/-- One or more `terms` calls in `t`, together covering `part` of `t`'s
import roots, rooted at `roots`, importing `ownMods`'s own constants
(which pulls in every dependency transitively) and expanding through an
owned constant always, through a dependency constant only when `keepDeps`
names it (`cmdTerms`'s own closure rule). Two independently-built
executable roots that each declare their own `main` cannot be in the same
`importModules` call (a genuine Lean limit, not one of `terms`'s making —
EquiVM's pins have exactly this shape, `Tests.DiffTest.Main` against
`Examples.ERC20.SpecTests`). `runTerms` recovers the way
`Shell.Target.declsOf` and `Shell.DepDiff.exportRows` already do for the
certificate and the dependency diff: on the clash Lean reports, drop the
named module from this call and retry; every module dropped this way runs
in its own later call, seeded from and excluded by the same, full
`ownMods` every call uses (`ownMods` never shrinks — only the import-root
list, `part`, does), and the union of every call's rows is the result. A
clash costs one extra probe call per colliding module, never a missing
root. -/
partial def runTerms (t : Tree) (ownMods keepDeps roots : List String)
    (part : List String := ownMods) : IO TermsOut := do
  if part.isEmpty then return { rows := [], missing := [] }
  let rec go (cur moved : List String) : IO (String × List String) := do
    IO.FS.writeFile t.request <| Json.compress <| Json.mkObj
      [("modules", toJson cur), ("ownMods", toJson ownMods),
       ("keepDeps", toJson keepDeps.eraseDups), ("roots", toJson roots.eraseDups)]
    try
      let out ← t.probe #["terms", t.request.toString]
      pure (out, moved)
    catch e =>
      let some x := clashModule e.toString | throw e
      unless cur.length > 1 && cur.contains x do throw e
      go (cur.filter (· != x)) (moved ++ [x])
  let (out, moved) ← go part []
  let out1 ← parseOrThrow s!"probe terms at {t.toolchain}" (parseTerms out)
  if moved.isEmpty then return out1
  let out2 ← runTerms t ownMods keepDeps roots moved
  pure { rows := out1.rows ++ out2.rows, missing := out1.missing ++ out2.missing }

/-- Certify the computational equality of every Behavior finding of `fs`
(`docs/static-diff.md` § 4), given the dependency diff of `base` against
`after` (`LeanMend.Shell.DepDiff.computeDepDiff`, § 1, already cached per
pair of pins) and the open findings of this run (so a target constant that
reaches no finding of its own needs no body fetched: `ConstStatus.targetHeld`,
already held by the certificate's own axiom and statement check). Two
`terms` calls total, one per side, every finding's root batched together —
not one call per declaration (the cost rule,
`.scratch/static-diff-review.md`). `names.toAfter` gives the after-side
root of each finding (`f.decl.name` is already the baseline name, `compare`'s
own convention, `LeanMend.Core.Compare.Finding`); a nested constant's name
is read as the same string at both sides, the same assumption the
dependency diff's own join-by-name already makes (`LeanMend.Core.DepDiff.depDiff`). -/
def certifyBehaviors (names : Names) (base after : Tree) (allFindings : List Finding)
    (beh : List Finding) : IO (List (String × CompEqResult)) := do
  if beh.isEmpty then return []
  let (depEntries, _, _) ← computeDepDiff base.dir after.dir
  let depIdx : Std.HashMap String DepDiffKind :=
    depEntries.foldl (fun m e => m.insert e.name e.kind) {}
  let keepDeps := depEntries.map (·.name)
  let afterOwn ← builtModuleNames after.dir
  let baseOwn ← builtModuleNames base.dir
  let afterRoots := beh.map fun f => names.toAfter f.decl.name
  let baseRoots := beh.map fun f => f.decl.name
  let afterOut ← runTerms after afterOwn keepDeps afterRoots
  let baseOut ← runTerms base baseOwn keepDeps baseRoots
  let afterIdx := afterOut.rows.foldl (fun m (r : TermRow) => m.insert r.name r)
    ({} : Std.HashMap String TermRow)
  let baseIdx := baseOut.rows.foldl (fun m (r : TermRow) => m.insert r.name r)
    ({} : Std.HashMap String TermRow)
  let afterOwnSet : Std.HashSet String := afterOwn.foldl (fun s m => s.insert m) {}
  let openAxiom : Std.HashSet String := (allFindings.filter (·.reason == .axiomsDiffer)).foldl
    (fun s f => s.insert (names.toAfter f.decl.name)) {}
  let openBehavior : Std.HashSet String := beh.foldl
    (fun s f => s.insert (names.toAfter f.decl.name)) {}
  let depStatus (k : DepDiffKind) : ConstStatus :=
    match k with
    | .axioms .. => .dependencyTerminal "its axiom set differs between the two toolchains"
    | .body => .dependencyBodyDiffers
    | .onlyBefore => .dependencyTerminal "it exists at the old toolchain only"
    | .onlyAfter => .dependencyTerminal "it exists at the new toolchain only"
  let statusOf (n : String) : ConstStatus :=
    match afterIdx[n]? with
    | some r =>
      match r.trust with
      | some k => .trustPoint k
      | none =>
        if afterOwnSet.contains r.module then
          if openBehavior.contains n then .targetOpen
          else if openAxiom.contains n then .targetAxiomsDiffer
          else .targetHeld
        else match depIdx[n]? with
          | some k => depStatus k
          | none => .dependencyUnchanged
    | none =>
      match depIdx[n]? with
      | some k => depStatus k
      | none => .dependencyUnchanged
  let bodyOf (n : String) : Option (ErasedTerm × ErasedTerm) := do
    let a ← afterIdx[n]?
    let ab ← a.body
    let b ← baseIdx[n]?
    let bb ← b.body
    pure (bb, ab)
  let eqnsOf (n : String) : Option (List Equation × List Equation) := do
    let a ← afterIdx[n]?
    let ae ← a.eqns
    let b ← baseIdx[n]?
    let be ← b.eqns
    pure (be, ae)
  let mut memo : Std.HashMap String CompEqResult := {}
  let mut results : List (String × CompEqResult) := []
  for f in beh do
    let n := names.toAfter f.decl.name
    let (r, memo') := certifyEqual bodyOf statusOf eqnsOf memo n
    memo := memo'
    results := results ++ [(n, r)]
  pure results

end LeanMend.Shell
