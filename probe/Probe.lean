import Lean

/-!
# The probe

Runs under the TARGET's toolchain, never lean-mend's
(`docs/architecture.md` § The version boundary, decision D3). The shell runs it
inside the target as

    lake env lean --run Probe.lean <command> <args>…

and reads one JSON value per line from stdout. It uses only core API that has
the same shape from v4.29.0 to v4.35.0; CI compiles it under each supported
toolchain.

Commands:

* `imports <file>…` — `{"file", "imports"}` per file, from the parsed header.
* `decls <module> <file>` — one line per declaration of `<module>` that has a
  source range: name, kind, statement text, body text, statement and body
  byte ranges, axioms. Needs the module built.
* `deprecated <module>…` — `{"name", "newName"}` for every `@[deprecated]`
  declaration in the environment of the given modules.
-/

open Lean

namespace LeanMendProbe

def emit (j : Json) : IO Unit := IO.println j.compress

/-- Every node of kind `k` in `stx`, in source order. -/
partial def nodesOfKind (k : SyntaxNodeKind) (stx : Syntax) : Array Syntax :=
  let here := if stx.getKind == k then #[stx] else #[]
  stx.getArgs.foldl (fun acc c => acc ++ nodesOfKind k c) here

/-- The first node whose kind is in `ks`, depth first. -/
partial def firstOfKinds (ks : List SyntaxNodeKind) (stx : Syntax) : Option Syntax :=
  if ks.contains stx.getKind then some stx
  else stx.getArgs.foldl (fun acc c => acc <|> firstOfKinds ks c) none

/-- A byte range `[start, stop)` of a syntax node. Only `Nat` is named, because
the position types differ between toolchains. -/
def byteRange (stx : Syntax) : Option (Nat × Nat) := do
  let a ← stx.getPos?
  let b ← stx.getTailPos?
  pure (a.byteIdx, b.byteIdx)

def rangeJson (r : Nat × Nat) : Json :=
  Json.arr #[toJson r.1, toJson r.2]

def textOf (src : ByteArray) (r : Nat × Nat) : String :=
  String.fromUTF8! (src.extract r.1 r.2)

def cmdImports (files : List String) : IO Unit := do
  for f in files do
    let src ← IO.FS.readFile f
    let ictx := Parser.mkInputContext src f
    let (hdr, _, _) ← Parser.parseHeader ictx
    let names := (nodesOfKind ``Parser.Module.import hdr.raw).filterMap fun imp =>
      (imp.getArgs.find? (·.isIdent)).map (·.getId.toString)
    emit <| Json.mkObj [("file", toJson f), ("imports", toJson names)]

def kindOf (env : Environment) (n : Name) : ConstantInfo → String
  | .thmInfo _ => "theorem"
  | .axiomInfo _ => "axiom"
  | .defnInfo d =>
    if (Meta.instanceExtension.getState env).instanceNames.contains n then "instance"
    else match d.hints with
      | .abbrev => "abbrev"
      | _ => "def"
  | _ => "other"

/-- Statement and body byte ranges of one parsed declaration command. -/
def regions (stx : Syntax) : Option ((Nat × Nat) × (Nat × Nat)) := do
  let sig ← firstOfKinds [``Parser.Command.declSig, ``Parser.Command.optDeclSig] stx
  let body ← firstOfKinds
    [``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
     ``Parser.Command.whereStructInst] stx
  let b ← byteRange body
  -- An empty signature (`abbrev T := Nat`) has no position: its statement
  -- region is the empty range where the body starts.
  pure ((byteRange sig).getD (b.1, b.1), b)

def cmdDecls (module : String) (file : String) : IO Unit := do
  let modName := module.toName
  let env ← importModules #[{ module := modName }] {} (loadExts := true)
  let src ← IO.FS.readFile file
  let bytes := src.toUTF8
  let ictx := Parser.mkInputContext src file
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let some idx := env.getModuleIdx? modName
    | throw <| IO.userError s!"module {module} is not in its own environment"
  let ctx : Core.Context := { fileName := file, fileMap := ictx.fileMap }
  for (n, ci) in env.constants.toList do
    if n.isInternal || env.getModuleIdxFor? n != some idx then continue
    let some ranges := declRangeExt.find? env n | continue
    let (stx, _, _) := Parser.parseCommand ictx pmctx
      { pos := ictx.fileMap.ofPosition ranges.range.pos } {}
    let some (sig, body) := regions stx | continue
    let (axioms, _) ← (collectAxioms n : CoreM _).toIO ctx { env }
    emit <| Json.mkObj
      [("name", toJson n.toString), ("module", toJson module),
       ("kind", toJson (kindOf env n ci)),
       ("statement", toJson (textOf bytes sig)), ("statementRange", rangeJson sig),
       ("body", toJson (textOf bytes body)), ("bodyRange", rangeJson body),
       ("axioms", toJson (axioms.map (·.toString)))]

def cmdDeprecated (modules : List String) : IO Unit := do
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {}
    (loadExts := true)
  for (n, _) in env.constants.toList do
    if let some e := Linter.deprecatedAttr.getParam? env n then
      emit <| Json.mkObj
        [("name", toJson n.toString),
         ("newName", toJson (e.newName?.map (·.toString)))]

end LeanMendProbe

open LeanMendProbe in
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  match args with
  | "imports" :: files => cmdImports files
  | ["decls", m, f] => cmdDecls m f
  | "deprecated" :: ms => cmdDeprecated ms
  | _ =>
    IO.eprintln "usage: imports <file>… | decls <module> <file> | deprecated <module>…"
    return 2
  return 0
