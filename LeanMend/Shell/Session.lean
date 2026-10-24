import Lean.Data.Json
import LeanMend.Core.Run
import LeanMend.Shell.Target

/-!
# Session and cards

When a run reaches `certificate`, the shell saves what `RunState.close` needs
(`.lean-mend/session.json`) and writes one card per finding
(`.lean-mend/cards/<id>.md`). `lean-mend judge` loads the session, replays the
judgments in the ledger, and steps the machine with the new judgment. See
`docs/verification.md` § Cards. JSON stays in the shell (concept B2).

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
   ("decls", Json.arr (c.decls.toArray.map declJson))]

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
         decls := ← (← get (α := List Json) j "decls").mapM declOf }

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

/-- What `RunState.close` needs, saved at `certificate`. -/
structure Session where
  target : String
  /-- The commit where `lean-mend/mend` starts. -/
  start : String
  base : Certificate
  after : Certificate
  mods : List Module
  aliases : AliasMap
  residue : List String
  cards : List Card

def sessionJson (s : Session) : Json := Json.mkObj
  [("target", toJson s.target), ("start", toJson s.start), ("base", certJson s.base), ("after", certJson s.after),
   ("mods", Json.arr (s.mods.toArray.map fun m =>
      Json.mkObj [("name", toJson m.name), ("imports", toJson m.imports)])),
   ("aliases", Json.arr (s.aliases.pairs.toArray.map fun (a, b) => toJson [a, b])),
   ("residue", toJson s.residue),
   ("cards", Json.arr (s.cards.toArray.map fun c => Json.mkObj
      [("id", toJson c.id), ("kind", toJson (cardKindName c.kind)), ("subject", toJson c.subject)]))]

def sessionOf (j : Json) : Except String Session := do
  let mods ← (← get (α := List Json) j "mods").mapM fun m => do
    pure ({ name := ← get m "name", imports := ← get m "imports" } : Module)
  let pairs ← (← get (α := List (List String)) j "aliases").mapM fun
    | [a, b] => pure (a, b)
    | _ => throw "session field 'aliases': not a pair"
  let cards ← (← get (α := List Json) j "cards").mapM fun c => do
    pure ({ id := ← get c "id", kind := ← cardKindOf (← get c "kind"),
            subject := ← get c "subject" } : Card)
  pure { target := ← get j "target", start := ← get j "start", base := ← certOf (← get j "base"),
         after := ← certOf (← get j "after"), mods, aliases := ⟨pairs⟩,
         residue := ← get j "residue", cards }

def sessionPath (target : FilePath) : FilePath := target / ".lean-mend" / "session.json"

def Session.context (s : Session) : Context :=
  { target := s.target, base := s.base, mods := s.mods, aliases := s.aliases }

/-- The card text (`docs/verification.md` § Cards): only generated data. -/
def cardText (c : Card) (f : Finding) (after : Certificate) (trace : List String) : String :=
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
  s!"**Evidence.**\n{evidence}\n\n" ++
  s!"**Trace.** Commits on lean-mend/mend that touch the module:\n" ++
    String.join (trace.map (s!"- {·}\n")) ++
  s!"\n**Counterexample.** None computed.\n\n" ++
  s!"Answer: `lean-mend judge <target> {c.id} accept|reject --by <name>`\n"

/-- Save the session and write one card per finding. -/
def writeCards (target : FilePath) (s : Session) (fs : List Finding)
    (fileOf : String → FilePath) : IO Unit := do
  IO.FS.writeFile (sessionPath target) (sessionJson s).pretty
  let dir := target / ".lean-mend" / "cards"
  IO.FS.createDirAll dir
  for (c, f) in s.cards.zip fs do
    let (_, log, _) ← run target "git"
      #["log", "--format=%h %s", s!"{s.start}..lean-mend/mend", "--", (fileOf f.decl.module).toString]
    IO.FS.writeFile (dir / s!"{c.id}.md")
      (cardText c f s.after ((log.splitOn "\n").filter (· ≠ "")))

end LeanMend.Shell
