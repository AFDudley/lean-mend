import Lean.Data.Json
import LeanMend.Core.Cause
import LeanMend.Core.Compare
import LeanMend.Shell.Target

/-!
# The evidence of the cards

IO that gathers what a card needs to state the cause of its finding
(`docs/verification.md` § What a card explains): the probe's `explain` and
`proofs` at each toolchain, the lake manifests, and `git log -L`. The Core
(`LeanMend.Core.Cause`) computes the paths, the causes and the groups from
this data. JSON stays in the shell (concept B2).

The data is gathered at `certificate`, when the findings are known: the base
worktree still holds the old toolchain's build then. Each side imports the
modules of the findings once (`explain`). The paths of the new toolchain name
constants that a declaration does not reach at the old one, so the old side
gets them as roots too (`pathLookups`); a removed axiom does the same the
other way, with one more `explain` run at the new toolchain.
-/

namespace LeanMend.Shell

open Lean (Json toJson)
open System (FilePath)

/-- One toolchain's tree, for the probe runs of `collectEvidence`. -/
structure Tree where
  dir : FilePath
  toolchain : String
  files : List (Module × FilePath)
  /-- The commit of the tree: the owner revision of the target's own modules. -/
  commit : String
  /-- Run one probe command in `dir` (`Target.probe`). -/
  probe : Array String → IO String
  /-- The absolute path of the request file of `explain`. -/
  request : FilePath

def Tree.fileOf (t : Tree) (module : String) : FilePath :=
  ((t.files.find? (·.1.name == module)).map (·.2)).getD module

private def get {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"field '{k}': {e}"

/-- The root package name and `(package, rev)` of `dir/lake-manifest.json`,
or none when the tree has no manifest. -/
def manifestRevs (dir : FilePath) : IO (Option (String × List (String × String))) := do
  let p := dir / "lake-manifest.json"
  unless ← p.pathExists do return none
  let txt ← IO.FS.readFile p
  parseOrThrow s!"{p}" do
    let j ← Json.parse txt
    let pkgs : List Json ← get j "packages"
    -- A path package has no `rev`: the card names it so.
    let revs ← pkgs.mapM fun q => do
      pure ((← get q "name" : String),
            ((q.getObjValAs? String "rev").toOption.getD "a path package, no rev in lake-manifest.json"))
    pure (some ((← get j "name" : String), revs))

/-- The owner of a module, from the `.olean` file that Lean loads it from:
under the toolchain's root, Lean core (also Std and Lake) at the toolchain;
under `.lake/packages/<p>/`, the package `p` at its manifest `rev`; else the
target itself at its commit. -/
def ownerOfOlean (sysroot : String) (t : Tree) (manifest : Option (String × List (String × String)))
    (olean : String) : Owner :=
  if olean.startsWith sysroot then ⟨"Lean core", t.toolchain⟩ else
  let parts := olean.splitOn "/.lake/packages/"
  if parts.length > 1 then
    let p := ((parts.getLast!).splitOn "/").head!
    match manifest with
    | some (_, revs) => ⟨p, (revs.lookup p).getD "not in lake-manifest.json"⟩
    | none => ⟨p, "no lake-manifest.json"⟩
  else ⟨(manifest.map (·.1)).getD "the target", t.commit⟩

/-- The output of one `explain` run: the side's data, and the body of each
row (its text and its start; the proofs come from `proofs`). -/
structure ExplainOut where
  side : Side
  rows : List (String × Body)

/-- Parse the lines of `explain` (`probe/Probe.lean`, `cmdExplain`). -/
def parseExplain (t : Tree) (manifest : Option (String × List (String × String))) (out : String) :
    Except String ExplainOut := do
  let lines ← (out.splitOn "\n" |>.filter (· ≠ "")).mapM Json.parse
  let mut consts := #[]
  let mut rows := #[]
  let mut missing := #[]
  let mut oleans := #[]
  let mut sysroot := none
  for j in lines do
    if let .ok (n : String) := j.getObjValAs? String "const" then
      let raw : List String ← get j "axioms"
      let isAx : Bool ← get j "axiom"
      let isCongr : Bool := (j.getObjValAs? Bool "congr").toOption.getD false
      consts := consts.push
        { name := n, module := ← get j "module", axioms := Parse.axiomSet raw, uses := ← get j "uses",
          axiomName := if isAx then (Parse.axiomSet [n]).head? else none, congr := isCongr : Const }
    else if let .ok (n : String) := j.getObjValAs? String "missing" then missing := missing.push n
    else if let .ok (m : String) := j.getObjValAs? String "moduleFile" then
      oleans := oleans.push (m, (← get j "olean" : String))
    else if let .ok (s : String) := j.getObjValAs? String "sysroot" then sysroot := some s
    else if (j.getObjVal? "unread").isOk then pure ()
    else
      let r : List Nat ← get j "bodyRange"
      rows := rows.push ((← get j "name" : String), { text := ← get j "body", start := r.head!, proofs := [] : Body })
  let some sys := sysroot | throw "explain: no sysroot line"
  pure { side := { toolchain := t.toolchain, consts := consts.toList, missing := missing.toList,
                   owners := oleans.toList.map fun (m, o) => (m, ownerOfOlean sys t manifest o) },
         rows := rows.toList }

/-- One `explain` run in `t`. -/
def runExplain (t : Tree) (modules rows roots : List String) : IO ExplainOut := do
  let mods := modules.eraseDups.map fun m => toJson [m, (t.fileOf m).toString]
  IO.FS.writeFile t.request <| Json.compress <| Json.mkObj
    [("modules", Json.arr mods.toArray), ("rows", toJson rows.eraseDups), ("roots", toJson roots.eraseDups)]
  let out ← t.probe #["explain", t.request.toString]
  parseOrThrow s!"probe explain at {t.toolchain}" (parseExplain t (← manifestRevs t.dir) out)

/-- The maximal proof ranges inside each of `ranges` of `file` (`proofs`). -/
def runProofs (t : Tree) (file : FilePath) (ranges : List (Nat × Nat)) : IO (List (List (Nat × Nat))) := do
  if ranges.isEmpty then return []
  let out ← t.probe (#["proofs", file.toString] ++ (ranges.flatMap fun (a, b) => [toString a, toString b]).toArray)
  parseOrThrow s!"probe proofs at {t.toolchain}" <|
    (out.splitOn "\n" |>.filter (· ≠ "")).mapM fun l => do
      let j ← Json.parse l
      let ps : List (List Nat) ← get j "proofs"
      pure (ps.map fun p => (p.head!, p.getLast!))

/-- The line (from 1) of byte offset `pos` in `text`. -/
def lineOf (text : ByteArray) (pos : Nat) : Nat :=
  (text.extract 0 pos).foldl (fun n b => if b == 10 then n + 1 else n) 1

/-- The commits from the parent of `start` (the baseline commit) to
`lean-mend/mend` that changed the lines of `range` in `file` (`git log -L`).
`start` itself is the bump commit. -/
def bodyCommits (target : FilePath) (start : String) (file : FilePath) (range : Nat × Nat) :
    IO (List BodyCommit) := do
  if range.1 ≥ range.2 then return []
  let text ← IO.FS.readBinFile (target / file)
  let l1 := lineOf text range.1
  let l2 := lineOf text (range.2 - 1)
  let out ← runOk target "git"
    #["log", s!"-L{l1},{l2}:{file}", "-s", "--format=%H%x1f%s%x1f%b%x1e", s!"{start}^..lean-mend/mend"]
  pure <| ((out.splitOn "\x1e").map String.trimAscii |>.map (·.toString) |>.filter (· ≠ "")).map fun r =>
    let fs := r.splitOn "\x1f"
    let sha := fs.head!
    let rule := ((fs.getD 2 "").splitOn "\n").findSome? fun l =>
      if l.startsWith "Rule: " then some (l.drop 6).toString else none
    { sha, subject := fs.getD 1 "", rule := if sha == start then none else rule, bump := sha == start }

/-- Gather the evidence of the cards of `fs` (`docs/verification.md` § What a
card explains). `base` and `after` are the trees of the two certificates. -/
def collectEvidence (names : Names) (base after : Tree) (target : FilePath) (start : String)
    (afterCert : Certificate) (fs : List Finding) : IO Evidence := do
  let pairs := fs.map fun f =>
    (f, (afterCert.decls.find? (·.name == names.toAfter f.decl.name)))
  let viol := pairs.filterMap fun (f, a?) => if f.reason == .axiomsDiffer then a?.map (f.decl, ·) else none
  let aOut ← runExplain after (pairs.filterMap (·.2.map (·.module)))
    (pairs.filterMap (·.2.map (·.name))) (viol.map (·.2.name))
  let added := viol.flatMap fun (b, a) => (a.axioms.filter (· ∉ b.axioms)).map (a.name, ·)
  let lookBase := pathLookups aOut.side added names.toBase
  let bOut ← runExplain base (fs.map (·.decl.module)) (fs.map (·.decl.name))
    (viol.map (·.1.name) ++ lookBase)
  let removed := viol.flatMap fun (b, a) => (b.axioms.filter (· ∉ a.axioms)).map (b.name, ·)
  let aIdx := aOut.side.index
  let lookAfter := (pathLookups bOut.side removed fun n => [names.toAfter n]).filter fun n =>
    !aIdx.contains n && n ∉ aOut.side.missing
  -- The module list stays that of the findings: the environment is the same.
  let afterSide ← if lookAfter.isEmpty then pure aOut.side else do
    let more ← runExplain after (pairs.filterMap (·.2.map (·.module))) [] lookAfter
    pure (aOut.side.merge more.side)
  -- Behavior: the bodies and their proofs, one `proofs` run per file and side.
  let beh := pairs.filterMap fun (f, a?) => if f.reason == .definitionChanged then a?.map (f.decl, ·) else none
  let withProofs (t : Tree) (rows : List (String × Body)) (ds : List (String × String)) :
      IO (List (String × Body)) := do
    let mut out := []
    for m in (ds.map (·.2)).eraseDups do
      let here := ds.filter (·.2 == m) |>.filterMap fun (n, _) => (rows.lookup n).map (n, ·)
      let ps ← runProofs t (t.fileOf m) (here.map fun (_, b) => (b.start, b.start + b.text.utf8ByteSize))
      out := out ++ (here.zip ps).map fun ((n, b), p) => (n, { b with proofs := p })
    pure out
  let bBodies ← withProofs base bOut.rows (beh.map fun (b, _) => (b.name, b.module))
  let aBodies ← withProofs after aOut.rows (beh.map fun (_, a) => (a.name, a.module))
  let bodies := beh.filterMap fun (b, a) => do
    pure (a.name, ← bBodies.lookup b.name, ← aBodies.lookup a.name)
  let mut commits := []
  for (_, a?) in pairs do
    if let some a := a? then
      if let some body := aOut.rows.lookup a.name then
        let cs ← bodyCommits target start (after.fileOf a.module)
          (body.start, body.start + body.text.utf8ByteSize)
        commits := commits ++ [(a.name, cs)]
  pure { base := bOut.side, after := afterSide, bodies, commits }

/-! ## JSON of the evidence, for the session -/

def constJson (c : Const) : Json :=
  Json.arr #[toJson c.name, toJson c.module, toJson c.axioms, toJson c.uses, toJson c.axiomName,
             toJson c.congr]

def constOf (j : Json) : Except String Const := do
  let .arr #[n, m, ax, us, an, cg] := j
    | throw "evidence: a constant is not [name, module, axioms, uses, axiom, congr]"
  pure { name := ← Lean.fromJson? n, module := ← Lean.fromJson? m, axioms := ← Lean.fromJson? ax,
         uses := ← Lean.fromJson? us, axiomName := ← Lean.fromJson? an, congr := ← Lean.fromJson? cg }

def sideJson (s : Side) : Json := Json.mkObj
  [("toolchain", toJson s.toolchain), ("consts", Json.arr (s.consts.toArray.map constJson)),
   ("owners", Json.arr (s.owners.toArray.map fun (m, o) => toJson [m, o.package, o.rev])),
   ("missing", toJson s.missing)]

def sideOf (j : Json) : Except String Side := do
  let cs : List Json ← get j "consts"
  let os : List (List String) ← get j "owners"
  pure { toolchain := ← get j "toolchain", consts := ← cs.mapM constOf, missing := ← get j "missing",
         owners := ← os.mapM fun
           | [m, p, r] => pure (m, ⟨p, r⟩)
           | _ => throw "evidence: an owner is not [module, package, rev]" }

def bodyJson (b : Body) : Json := Json.mkObj
  [("text", toJson b.text), ("start", toJson b.start),
   ("proofs", toJson (b.proofs.map fun (s, e) => [s, e]))]

def bodyOf (j : Json) : Except String Body := do
  let ps : List (List Nat) ← get j "proofs"
  pure { text := ← get j "text", start := ← get j "start", proofs := ps.map fun p => (p.head!, p.getLast!) }

def commitJson (c : BodyCommit) : Json := Json.mkObj
  [("sha", toJson c.sha), ("subject", toJson c.subject), ("rule", toJson c.rule), ("bump", toJson c.bump)]

def commitOf (j : Json) : Except String BodyCommit := do
  pure { sha := ← get j "sha", subject := ← get j "subject", rule := ← get j "rule", bump := ← get j "bump" }

def evidenceJson (e : Evidence) : Json := Json.mkObj
  [("base", sideJson e.base), ("after", sideJson e.after),
   ("bodies", Json.arr (e.bodies.toArray.map fun (n, b, a) =>
      Json.mkObj [("decl", toJson n), ("before", bodyJson b), ("after", bodyJson a)])),
   ("commits", Json.arr (e.commits.toArray.map fun (n, cs) =>
      Json.mkObj [("decl", toJson n), ("commits", Json.arr (cs.toArray.map commitJson))]))]

def evidenceOf (j : Json) : Except String Evidence := do
  let bs : List Json ← get j "bodies"
  let cs : List Json ← get j "commits"
  pure { base := ← sideOf (← get j "base"), after := ← sideOf (← get j "after"),
         bodies := ← bs.mapM fun b => do
           pure ((← get b "decl" : String), ← bodyOf (← get b "before"), ← bodyOf (← get b "after"))
         commits := ← cs.mapM fun c => do
           let l : List Json ← get c "commits"
           pure ((← get c "decl" : String), ← l.mapM commitOf) }

end LeanMend.Shell
