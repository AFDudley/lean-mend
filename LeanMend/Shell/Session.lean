import Lean.Data.Json
import LeanMend.Core.Run
import LeanMend.Core.Cause
import LeanMend.Shell.Target
import LeanMend.Shell.Cause

/-!
# Session and cards

When a run reaches `certificate`, the shell saves what `RunState.close` needs
and the evidence of the cards (`.lean-mend/session.json`), and writes one card
per finding (`.lean-mend/cards/<id>.md`) and one file of causes
(`.lean-mend/cards/causes.md`). `lean-mend judge` loads the session, replays
the judgments in the ledger, and steps the machine with the new judgment. See
`docs/verification.md` § Cards and § What a card explains. JSON stays in the
shell (concept B2).

Not built yet: a rejected Behavior card does not revert its patch. The
judgment is recorded and the finding stays open.
-/

namespace LeanMend.Shell

open Lean (Json toJson)
open System (FilePath)

def declJson (d : Decl) : Json := Json.mkObj
  [("name", toJson d.name), ("module", toJson d.module),
   ("kind", toJson (toString (repr d.kind)).toLower),
   ("statementHash", toJson d.statementHash), ("bodyHash", toJson d.bodyHash),
   ("axioms", toJson d.axioms)]

def certJson (c : Certificate) : Json := Json.mkObj
  [("toolchain", toJson c.toolchain.name), ("built", toJson c.built),
   ("decls", Json.arr (c.decls.toArray.map declJson)), ("followed", toJson c.followed)]

private def get {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"session field '{k}': {e}"

def declOf (j : Json) : Except String Decl := do
  let kindTxt : String ← get j "kind"
  let kind ← Parse.declKind ((kindTxt.splitOn ".").getLast!)
  pure { name := ← get j "name", module := ← get j "module", kind,
         statementHash := ← get j "statementHash", bodyHash := ← get j "bodyHash",
         axioms := ← get j "axioms" }

def certOf (j : Json) : Except String Certificate := do
  pure { toolchain := ⟨← get j "toolchain"⟩, built := ← get j "built",
         decls := ← (← get (α := List Json) j "decls").mapM declOf,
         followed := ← get j "followed" }

def cardKindName : CardKind → String
  | .behavior => "behavior" | .violation => "violation" | .spec => "spec"
  | .decision => "decision" | .held => "held"

def cardKindOf : String → Except String CardKind
  | "behavior" => .ok .behavior | "violation" => .ok .violation | "spec" => .ok .spec
  | "decision" => .ok .decision | "held" => .ok .held
  | s => .error s!"unknown card kind '{s}'"

/-- One card: its id, kind, and the declaration (after the alias map) it asks about. -/
structure Card where
  id : String
  kind : CardKind
  subject : String

/-- What `RunState.close` needs, saved at `certificate`, and the evidence of
the cards. -/
structure Session where
  target : String
  /-- The commit where `lean-mend/mend` starts: the bump commit. Its parent is
  the baseline commit. -/
  start : String
  base : Certificate
  after : Certificate
  mods : List Module
  aliases : AliasMap
  residue : List String
  cards : List Card
  /-- What the cards explain (`collectEvidence`). A session that a lean-mend
  before this field wrote has none; `judge` does not read it. -/
  evidence : Option Evidence

def sessionJson (s : Session) : Json := Json.mkObj
  [("target", toJson s.target), ("start", toJson s.start), ("base", certJson s.base), ("after", certJson s.after),
   ("mods", Json.arr (s.mods.toArray.map fun m =>
      Json.mkObj [("name", toJson m.name), ("imports", toJson m.imports)])),
   ("aliases", Json.arr (s.aliases.pairs.toArray.map fun (a, b) => toJson [a, b])),
   ("residue", toJson s.residue),
   ("cards", Json.arr (s.cards.toArray.map fun c => Json.mkObj
      [("id", toJson c.id), ("kind", toJson (cardKindName c.kind)), ("subject", toJson c.subject)])),
   ("evidence", match s.evidence with | some e => evidenceJson e | none => Json.null)]

def sessionOf (j : Json) : Except String Session := do
  let mods ← (← get (α := List Json) j "mods").mapM fun m => do
    pure ({ name := ← get m "name", imports := ← get m "imports" } : Module)
  let pairs ← (← get (α := List (List String)) j "aliases").mapM fun
    | [a, b] => pure (a, b)
    | _ => throw "session field 'aliases': not a pair"
  let cards ← (← get (α := List Json) j "cards").mapM fun c => do
    pure ({ id := ← get c "id", kind := ← cardKindOf (← get c "kind"),
            subject := ← get c "subject" } : Card)
  let evidence ← match j.getObjValD "evidence" with
    | Json.null => pure none
    | e => some <$> evidenceOf e
  pure { target := ← get j "target", start := ← get j "start", base := ← certOf (← get j "base"),
         after := ← certOf (← get j "after"), mods, aliases := ⟨pairs⟩,
         residue := ← get j "residue", cards, evidence }

def sessionPath (target : FilePath) : FilePath := target / ".lean-mend" / "session.json"

def Session.context (s : Session) : Context :=
  { target := s.target, base := s.base, mods := s.mods, aliases := s.aliases }

/-! ## Card text (`docs/verification.md` § Cards): only generated data -/

def code (s : String) : String := s!"`{s}`"

def axiomList (as : List String) : String :=
  if as.isEmpty then "none" else ", ".intercalate (as.map code)

def ownerText : Option Owner → String
  | some o => s!"{o.package} {o.rev}"
  | none => "owner not known"

/-- One constant at one toolchain. -/
def presenceText (tc : String) : Presence → String
  | .present n m o as => s!"at {tc}: {code n} in module {code m} ({ownerText o}), axioms {axiomList as}"
  | .absent n => s!"at {tc}: no constant {code n} in the environment of the findings' modules"

/-- A path, with the cause in bold. -/
def pathText (cause : String) (ns : List String) : String :=
  " → ".intercalate (ns.map fun n => if n == cause then s!"**{code n}**" else code n)

/-- The cards of a group, by id. -/
def membersText (ms : List (String × String × List String)) : String :=
  ", ".intercalate (ms.map (·.1))

/-- The cause section of a Violation card. -/
def violationText (baseTc afterTc : String) (groups : List CauseGroup)
    (xs : List AxiomExplanation) : String :=
  String.join <| xs.map fun x =>
    let others := match groups.zipIdx.find? (·.1.key == x.key) with
      | some (g, i) =>
        s!"  - Cause group {i + 1} of `causes.md`: {g.members.length} card(s): {membersText g.members}.\n"
      | none => ""
    match x with
    | .notComputed ax ch reason =>
      s!"- {code ax}, {if ch == .added then "added" else "removed"}: the cause is not computed: {reason}.\n" ++ others
    | .cause c =>
      let (here, there) := if c.change == .added then (afterTc, baseTc) else (baseTc, afterTc)
      let cn := c.cause.here.name
      s!"- {code c.axiom_}, {if c.change == .added then s!"added at {afterTc}" else s!"removed at {afterTc}"}.\n" ++
      s!"  - Path at {here}: {pathText cn (c.path.map (·.here.name))}.\n" ++
      (match c.otherPath with
        | .ok p => s!"  - Path at {there} to the cause: {pathText c.cause.there.name p}. {code c.axiom_} is not on it.\n"
        | .error e => s!"  - Path at {there}: not computed: {e}.\n") ++
      s!"  - Cause: {code cn}, the constant on the path nearest {code c.axiom_} whose own axiom set differs " ++
        s!"between the toolchains.\n" ++
      s!"    - {presenceText here c.cause.here}\n" ++
      s!"    - {presenceText there c.cause.there}\n" ++ others

/-- A hunk as unified diff lines. -/
def hunkText (h : Hunk) : String :=
  s!"@@ -{h.beforeLine + 1},{h.removed.length} +{h.afterLine + 1},{h.added.length} @@\n" ++
  String.join (h.removed.map (s!"-{·}\n")) ++ String.join (h.added.map (s!"+{·}\n"))

/-- The cause section of a Behavior card. -/
def behaviorText (baseTc afterTc : String) : Option (Body × Body) → String
  | none => "The body diff is not computed: the probe gave no body row for the declaration at one toolchain.\n"
  | some (b, a) =>
    let ch := bodyChange b a
    let verdict :=
      if ch.hunks.isEmpty then
        "The body texts are equal; the body hash differs only after the alias map. No byte changed."
      else if ch.proofOnly then
        s!"The change is in proofs only: every changed byte lies inside a proof at {baseTc} and at {afterTc}. " ++
        "A proof does not change what the definition computes."
      else
        s!"The change is not in proofs only: {ch.outside.length} of {ch.hunks.length} hunk(s) change bytes " ++
        "outside a proof: " ++ ", ".intercalate (ch.outside.map fun h => s!"line {h.afterLine + 1}") ++ "."
    s!"{verdict}\n\nThe body diff, from {baseTc} to {afterTc} (lines of the body):\n\n```diff\n" ++
      String.join (ch.hunks.map hunkText) ++ "```\n"

/-- The commits that changed a body. -/
def commitsText (rules : List (String × String × Nat)) : Option (List BodyCommit) → String
  | none => "- not computed: the probe gave no body row for the declaration at the new toolchain\n"
  | some [] => "- none\n"
  | some cs => String.join <| cs.map fun c =>
    let short := (c.sha.take 12).toString
    if c.bump then
      s!"- {short} {c.subject}: the bump commit, the input of `--adopt`. It is not a commit of this run, " ++
        "so the ledger has no rule for it.\n"
    else match c.rule with
      | some r =>
        let ledger := (rules.filter (·.1 == r)).map fun (_, m, e) => s!"`rebuilt` in {code m}, errors after {e}"
        s!"- {short} {c.subject}: rule {code r}" ++
          (if ledger.isEmpty then "; the ledger has no `rebuilt` entry with this rule" else s!"; ledger: {", ".intercalate ledger}") ++
          ".\n"
      | none => s!"- {short} {c.subject}: no `Rule:` line in the commit message.\n"

/-- The ledger entries of one site (`docs/verification.md` § Cards, Trace):
the diagnosed sites in the declaration, and the attempts and the end of the
mend of its module. -/
def traceLines (ledger : List Json) (module decl : String) : List String := Id.run do
  let mut out := #[]
  let mut cur := ""
  for j in ledger do
    let obs := (j.getObjValAs? String "obs").toOption.getD ""
    let d := j.getObjValD "detail"
    match obs with
    | "diagnosed" =>
      if (d.getObjValAs? String "module").toOption == some module then
        let sites := (d.getObjValAs? (List Json) "detail").toOption.getD []
        for s in sites do
          if (s.getObjValAs? String "decl").toOption == some decl then
            let cls := (s.getObjValAs? String "class").toOption.getD "?"
            let line := (s.getObjValAs? Nat "line").toOption.getD 0
            let n := (s.getObjValAs? Nat "candidates").toOption.getD 0
            out := out.push s!"`diagnosed`: {cls} at line {line}, {n} candidate(s)"
    | "moduleAttempt" => cur := (d.getObjValAs? String "module").toOption.getD ""
    | "rebuilt" =>
      if cur == module then
        let rule := (d.getObjValAs? String "rule").toOption.getD "?"
        let e := (d.getObjValAs? Nat "errors").toOption.getD 0
        out := out.push s!"`rebuilt`: rule {code rule}, errors after {e}"
    | "mended" =>
      if (d.getStr?).toOption == some module then out := out.push s!"`mended`: {code module}"
    | _ => pure ()
  return out.toList

/-- `(rule, module, errors)` of every `rebuilt` entry of the ledger. -/
def rebuiltRules (ledger : List Json) : List (String × String × Nat) := Id.run do
  let mut out := #[]
  let mut cur := ""
  for j in ledger do
    let d := j.getObjValD "detail"
    match (j.getObjValAs? String "obs").toOption.getD "" with
    | "moduleAttempt" => cur := (d.getObjValAs? String "module").toOption.getD ""
    | "rebuilt" =>
      out := out.push ((d.getObjValAs? String "rule").toOption.getD "", cur,
                       (d.getObjValAs? Nat "errors").toOption.getD 0)
    | _ => pure ()
  return out.toList

/-- What one card shows besides its finding. -/
structure CardData where
  trace : List String
  commits : Option (List BodyCommit)
  /-- `rebuiltRules` of the ledger. -/
  rules : List (String × String × Nat)
  cause : String

/-- The card text (`docs/verification.md` § Cards): only generated data. -/
def cardText (c : Card) (f : Finding) (after : Certificate) (d : CardData) : String :=
  let a? : Option Decl := after.decls.find? (·.name == c.subject)
  let status := "undecided"
  let evidence := match f.reason with
    | .axiomsDiffer =>
      s!"- baseline axioms: {f.decl.axioms}\n- after axioms: {(a?.map Decl.axioms).getD []}"
    | .definitionChanged =>
      s!"- body hash before: {f.decl.bodyHash}\n- body hash after: {(a?.map Decl.bodyHash).getD "?"}"
    | r => s!"- {repr r}"
  s!"# Card {c.id}: {cardKindName c.kind}\n\n" ++
  s!"**Rule.** No harm (docs/machine.md § The invariant), part " ++
    s!"{if c.kind == .violation then "2: the axioms of a declaration are unchanged" else "3: a changed definition body needs a judgment"}.\n\n" ++
  s!"**Subject.** `{c.subject}` in module `{f.decl.module}`.\n\n" ++
  s!"**Status.** {status}.\n\n" ++
  s!"**Cause.**\n{d.cause}\n" ++
  s!"**Evidence.**\n{evidence}\n\n" ++
  s!"**Trace.** Ledger entries for `{c.subject}` in `{f.decl.module}`:\n" ++
    (if d.trace.isEmpty then "- none\n" else String.join (d.trace.map (s!"- {·}\n"))) ++
  s!"\nCommits that changed the body, from the baseline commit to `lean-mend/mend`:\n" ++
    commitsText d.rules d.commits ++
  s!"\n**Counterexample.** None computed.\n\n" ++
  s!"Answer: `lean-mend judge <target> {c.id} accept|reject --by <name>`\n"

/-- `causes.md`: one section per cause, with each card it explains. Each card
keeps its own id, and a judgment answers one card (`docs/verification.md`
§ What a card explains). -/
def causesText (baseTc afterTc : String) (groups : List CauseGroup)
    (bodies : List (List BodyCommit × List (String × String))) : String :=
  let vs := groups.zipIdx.map fun (g, i) =>
    let head := match g.key with
      | .const n m ch => s!"## Cause {i + 1}: {code n} in module {code m}, {if ch == .added then "adds" else "removes"} an axiom\n\n"
      | .notComputed r => s!"## Cause {i + 1}: not computed\n\n{r}.\n\n"
    let detail := match g.first with
      | .cause c =>
        let (here, there) := if c.change == .added then (afterTc, baseTc) else (baseTc, afterTc)
        s!"- {presenceText here c.cause.here}\n- {presenceText there c.cause.there}\n\n"
      | .notComputed .. => ""
    head ++ detail ++ s!"Cards ({g.members.length}):\n\n" ++
      String.join (g.members.map fun (id, decl, as) => s!"- {id} {code decl}: {axiomList as}\n") ++ "\n"
  let bs := bodies.zipIdx.map fun ((cs, ms), i) =>
    s!"## Body change {i + 1}: " ++
      (if cs.isEmpty then "no commit found" else ", ".intercalate (cs.map fun c => (c.sha.take 12).toString ++ (if c.bump then " (bump commit)" else ""))) ++
      "\n\n" ++ s!"Cards ({ms.length}):\n\n" ++ String.join (ms.map fun (id, decl) => s!"- {id} {code decl}\n") ++ "\n"
  "# Causes\n\nOne section per cause. Each card keeps its own id for `lean-mend judge`.\n\n" ++
    String.join vs ++ String.join bs


/-- `docs/static-diff.md` § 4: `LeanMend.Shell.Driver.autoAcceptCompEq`'s own
ledger note for `decl` (`"compEq"`, one per Behavior finding it examined,
certified or not). `none` when the check never ran for `decl` (the finding
closed by decision D16's proof-only check first, or an older ledger has no
such note). -/
def compEqNote (ledger : List Json) (decl : String) : Option Json :=
  ledger.findSome? fun j =>
    if (j.getObjValAs? String "obs").toOption == some "compEq" then
      let d := j.getObjValD "detail"
      if (d.getObjValAs? String "subject").toOption == some decl then some d else none
    else none

/-- The computational-equality section of a Behavior card
(`docs/static-diff.md` § 4, decision S3): the first differing subterm and
its constant, read back from `compEqNote`. A card exists at all only when
`certifyEqual` did not certify equality (`autoAcceptCompEq` auto-accepts
every other case with no card), so this section is always a `differsAt`
note once one is found. -/
def compEqText (ledger : List Json) (decl : String) : String :=
  match compEqNote ledger decl with
  | none => "- not computed: no `compEq` ledger note for this declaration\n"
  | some d =>
    match (d.getObjValAs? String "result").toOption with
    | some "differsAt" =>
      let cst := (d.getObjValAs? String "constant").toOption.getD "?"
      let reason := (d.getObjValAs? String "reason").toOption.getD "?"
      s!"- the first differing subterm is at {code cst}: {reason}\n"
    | _ => "- not computed: the ledger note does not name a differing subterm\n"

/-- Write one card per finding and `causes.md` into `dir`, from the session,
its evidence and the ledger. -/
def writeCards (dir : FilePath) (s : Session) (fs : List Finding) (ledger : List Json) : IO Unit := do
  IO.FS.createDirAll dir
  let baseTc := s.base.toolchain.name
  let afterTc := s.after.toolchain.name
  let names := Names.ofAliases s.aliases
  let rules := rebuiltRules ledger
  let cs : List (Card × Finding) := s.cards.zip fs
  let expl : List (Card × Finding × List AxiomExplanation) := cs.map fun (c, f) =>
    let a? := s.after.decls.find? fun (d : Decl) => d.name == c.subject
    match s.evidence, a? with
    | some e, some a =>
      (c, f, if f.reason == Reason.axiomsDiffer then explainViolation names e.base e.after f.decl a else [])
    | _, _ => (c, f, [])
  let groups := groupCauses (expl.filterMap fun (c, f, xs) =>
    if f.reason == Reason.axiomsDiffer then some (c.id, c.subject, xs) else none)
  let commitsOf (n : String) : Option (List BodyCommit) := s.evidence.bind (·.commits.lookup n)
  let bodies := groupBodies (cs.filterMap fun (c, f) =>
    if f.reason == .definitionChanged then some (c.id, c.subject, (commitsOf c.subject).getD []) else none)
  for (c, f, xs) in expl do
    let cause := match s.evidence, f.reason with
      | none, _ => "- not computed: the session holds no evidence (lean-mend before the evidence field wrote it)\n"
      | some _, .axiomsDiffer =>
        if xs.isEmpty then "- not computed: the after certificate has no row for the declaration\n"
        else violationText baseTc afterTc groups xs
      | some e, .definitionChanged =>
        behaviorText baseTc afterTc ((e.bodies.lookup c.subject).map fun (b, a) => (b, a)) ++
        "\nThe commits that changed the body, with their rules, are in Trace.\n" ++
        "\n**Computational equality** (`docs/static-diff.md` § 4):\n" ++ compEqText ledger c.subject
      | some _, _ => "- none: no card explains this reason\n"
    let d : CardData := { trace := traceLines ledger f.decl.module c.subject, commits := commitsOf c.subject,
                          rules, cause }
    IO.FS.writeFile (dir / s!"{c.id}.md") (cardText c f s.after d)
  IO.FS.writeFile (dir / "causes.md") (causesText baseTc afterTc groups bodies)

/-- The lines of the ledger, parsed. -/
def readLedger (ledger : FilePath) : IO (List Json) := do
  let lines := ((← IO.FS.readFile ledger).splitOn "\n").filter (· ≠ "")
  lines.mapM fun l => parseOrThrow "ledger" (Json.parse l)

/-- Save the session, then write the cards into `.lean-mend/cards`. -/
def saveSession (target : FilePath) (s : Session) (fs : List Finding) : IO Unit := do
  IO.FS.writeFile (sessionPath target) (sessionJson s).pretty
  writeCards (target / ".lean-mend" / "cards") s fs (← readLedger (target / ".lean-mend" / "ledger.jsonl"))

end LeanMend.Shell
