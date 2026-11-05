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
* `decls-batch <list>` — `decls` for every `module<TAB>file` line of `<list>`,
  from one environment.
* `regions <file>` — each declaration command of a file, parsed without
  elaboration: qualified name, command range, statement and body ranges.
* `node <file> <offset>…` — for each offset, the syntax nodes that contain it,
  innermost first, with kinds, ranges, and tokens for tactic, `open` and
  `match` nodes.
* `deprecated <module>…` — `{"name", "newName"}` for every `@[deprecated]`
  declaration in the environment of the given modules.
* `serve` — one JSON request per line of stdin, `{"file", "offsets"}`; one
  JSON reply per line of stdout, `{"regions", "nodes"}`: `regions <file>` and
  `node <file> <offsets>…` from one import, kept across requests and
  refreshed only when a request's file has a different import header
  (`docs/parallel.md` C1-C3). Ends at end of file on stdin.
-/

open Lean

namespace LeanMendProbe

/-- Print one JSON line and flush it: `serve`'s caller reads one reply per
request from a pipe, so a line that stays in stdio's buffer until the
process exits never arrives. -/
def emit (j : Json) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn j.compress
  out.flush

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
  | .inductInfo _ =>
    if isClass env n then "class" else if isStructure env n then "structure" else "inductive"
  | _ => "other"

/-- A declaration command that defines a type: its fields or constructors are
its statement, and it has no body. -/
def isTypeCommand (stx : Syntax) : Bool :=
  (firstOfKinds [``Parser.Command.inductive, ``Parser.Command.structure,
    ``Parser.Command.classInductive] stx).isSome

/-- Statement and body byte ranges of one parsed declaration command. A type
command (`inductive`, `structure`, `class`) has its whole text as the
statement and an empty body at its end (`docs/verification.md`). -/
def regions (stx : Syntax) : Option ((Nat × Nat) × (Nat × Nat)) := do
  if isTypeCommand stx then
    let r ← byteRange stx
    return (r, (r.2, r.2))
  let sig ← firstOfKinds [``Parser.Command.declSig, ``Parser.Command.optDeclSig] stx
  let body ← firstOfKinds
    [``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
     ``Parser.Command.whereStructInst] stx
  let b ← byteRange body
  -- An empty signature (`abbrev T := Nat`) has no position: its statement
  -- region is the empty range where the body starts.
  pure ((byteRange sig).getD (b.1, b.1), b)

/-- The imports of a parsed header: its explicit `import` lines, with the
implicit `Init` prepended unless the file declares `prelude`. Shared by every
command that builds the file's own environment, so `serve` can tell whether a
later request needs a new import (`docs/parallel.md` C2). -/
def headerImports (hdr : Syntax) : Array Name :=
  let explicit := (nodesOfKind ``Parser.Module.import hdr).filterMap fun imp =>
    (imp.getArgs.find? (·.isIdent)).map (·.getId)
  let isPrelude := !(nodesOfKind ``Parser.Module.prelude hdr).isEmpty
  if isPrelude then explicit else #[`Init] ++ explicit

/-- Every declaration command of a file, parsed but not elaborated, so it
works on a module that does not build: one JSON object per declaration, in
source order, the shape `regions <file>` emits one per line of. Names are
qualified by the enclosing `namespace` commands. Shared by `cmdRegions` and
`cmdServe`, from an environment either one already built. -/
partial def regionsArray (ictx : Parser.InputContext) (pmctx : Parser.ParserModuleContext)
    (st0 : Parser.ModuleParserState) (msgs0 : MessageLog) : IO (Array Json) := do
  -- The scope stack: `some ns` for a namespace, `none` for a section.
  let rec loop (st : Parser.ModuleParserState) (msgs : MessageLog)
      (scopes : List (Option Name)) (acc : Array Json) : IO (Array Json) := do
    let (stx, st', msgs') := Parser.parseCommand ictx pmctx st msgs
    if Parser.isTerminalCommand stx then return acc
    let k := stx.getKind
    let scopes :=
      if k == ``Parser.Command.namespace then
        (stx.getArgs.find? (·.isIdent)).map (·.getId) :: scopes
      else if k == ``Parser.Command.section then none :: scopes
      else if k == ``Parser.Command.end then scopes.drop 1
      else scopes
    -- A `mutual` block holds several declarations: report each one.
    let decls := if k == ``Parser.Command.mutual then nodesOfKind ``Parser.Command.declaration stx
      else #[stx]
    let mut acc := acc
    for d in decls do
      if let some (sig, body) := regions d then
        let written := (firstOfKinds [``Parser.Command.declId] d).bind fun i =>
          (i.getArgs.find? (·.isIdent)).map (·.getId)
        let pre := scopes.reverse.filterMap id |>.foldl (fun acc n => acc ++ n) Name.anonymous
        let name := written.map (fun w => (pre ++ w).toString) |>.getD ""
        if let some r := byteRange d then
          acc := acc.push <| Json.mkObj
            [("name", toJson name), ("range", rangeJson r),
             ("statementRange", rangeJson sig), ("bodyRange", rangeJson body)]
    loop st' msgs' scopes acc
  loop st0 msgs0 [] #[]

/-- `regions <file>`: the environment is the file's imports (they build,
because only a frontier module is read), so notation from imports parses;
notation defined in the same file does not. -/
def cmdRegions (file : String) : IO Unit := do
  let src ← IO.FS.readFile file
  let ictx := Parser.mkInputContext src file
  let (hdr, st0, msgs0) ← Parser.parseHeader ictx
  let env ← importModules ((headerImports hdr.raw).map fun n => { module := n }) {} (loadExts := true)
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  for j in ← regionsArray ictx pmctx st0 msgs0 do emit j

/-- The nodes of `stx` that contain byte offset `pos`, outermost first. -/
partial def pathTo (stx : Syntax) (pos : Nat) : List Syntax :=
  let here := match byteRange stx with
    | some (a, b) => a ≤ pos && pos < b
    | none => false
  if !here then []
  else
    match stx.getArgs.toList.findSome? fun c =>
        let p := pathTo c pos
        if p.isEmpty then none else some p with
    | some p => stx :: p
    | none => [stx]

/-- The atoms and identifiers of `stx`, in source order, with byte ranges. -/
partial def tokens (src : ByteArray) (stx : Syntax) : Array Json :=
  match stx with
  | .atom _ _ | .ident .. =>
    match byteRange stx with
    | some r => #[Json.mkObj [("text", toJson (textOf src r)), ("range", rangeJson r)]]
    | none => #[]
  | _ => stx.getArgs.foldl (fun acc c => acc ++ tokens src c) #[]

/-- The syntax nodes that contain byte offset `offset`, innermost first: kind
and byte range; tactic nodes (kind under `Lean.Parser.Tactic`) also carry
their tokens. `{"file", "offset", "nodes"}`, the shape `node <file>
<offset>…` emits one per line of. Shared by `cmdNode` and `cmdServe`, from an
environment either one already built.

`nodes` is empty when no parsed command contains `offset`. The parser has
only the imports' environment, so syntax that the file itself declares (a
`macro`, `syntax` or `notation` command) does not parse. The parser then
skips to the next command, and the bytes it skips are in no command. The
site at such an offset gets no node, so no rule that needs a node proposes a
candidate for it. -/
partial def nodeAt (ictx : Parser.InputContext) (pmctx : Parser.ParserModuleContext)
    (st0 : Parser.ModuleParserState) (msgs0 : MessageLog) (file : String) (bytes : ByteArray)
    (offset : Nat) : IO Json := do
  let reply (nodes : Array Json) : Json :=
    Json.mkObj [("file", toJson file), ("offset", toJson offset), ("nodes", Json.arr nodes)]
  let rec loop (st : Parser.ModuleParserState) (msgs : MessageLog) : IO Json := do
    let (stx, st', msgs') := Parser.parseCommand ictx pmctx st msgs
    if Parser.isTerminalCommand stx then return reply #[]
    match byteRange stx with
    | some (a, b) =>
      if a ≤ offset && offset < b then
        let nodes := (pathTo stx offset).reverse.filterMap fun n =>
          (byteRange n).map fun r =>
            let k := n.getKind
            let base := [("kind", toJson k.toString), ("range", rangeJson r)]
            if (`Lean.Parser.Tactic).isPrefixOf k || k == ``Parser.Command.open ||
                k == ``Parser.Term.match then
              Json.mkObj (base ++ [("tokens", Json.arr (tokens bytes n))])
            else Json.mkObj base
        pure (reply nodes.toArray)
      else loop st' msgs'
    | none => loop st' msgs'
  loop st0 msgs0

/-- `node <file> <offset>…`: the file is parsed, not elaborated, with the
environment of its imports plus `Init`. -/
def cmdNode (file : String) (offsets : List Nat) : IO Unit := do
  let src ← IO.FS.readFile file
  let bytes := src.toUTF8
  let ictx := Parser.mkInputContext src file
  let (hdr, st0, msgs0) ← Parser.parseHeader ictx
  let env ← importModules ((headerImports hdr.raw).map fun n => { module := n }) {} (loadExts := true)
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  for offset in offsets do
    emit (← nodeAt ictx pmctx st0 msgs0 file bytes offset)

/-- The state of `axiomsOf`: Tarjan's strongly connected components over the
constants, so that each constant's axiom set is computed once per process. -/
structure AxState where
  next : Nat := 0
  index : Std.HashMap Name Nat := {}
  low : Std.HashMap Name Nat := {}
  stack : Array Name := #[]
  onStack : Std.HashSet Name := {}
  /-- The axioms a constant on the stack reaches outside its component. -/
  acc : Std.HashMap Name (Std.HashSet Name) := {}
  /-- The axioms of every constant whose component is complete. -/
  done : Std.HashMap Name (Std.HashSet Name) := {}

/-- The edges of `Lean.CollectAxioms.collect` (Lean v4.29.0): the constant
itself when it is an axiom, and the constants that `collect` visits next. -/
def axEdges (env : Environment) (c : Name) : Std.HashSet Name × Array Name :=
  let used (e : Expr) := e.getUsedConstants
  match env.checked.get.find? c with
  | some (.axiomInfo v) => (({} : Std.HashSet Name).insert c, used v.type)
  | some (.defnInfo v) => ({}, used v.type ++ used v.value)
  | some (.thmInfo v) => ({}, used v.type ++ used v.value)
  | some (.opaqueInfo v) => ({}, used v.type ++ used v.value)
  | some (.quotInfo _) => ({}, #[])
  | some (.ctorInfo v) => ({}, used v.type)
  | some (.recInfo v) => ({}, used v.type)
  | some (.inductInfo v) => ({}, used v.type ++ v.ctors.toArray)
  | none => ({}, #[])

def nameUnion (a b : Std.HashSet Name) : Std.HashSet Name := b.fold (fun s n => s.insert n) a

/-- Visit `v` (Tarjan). Every constant of a component gets the union of the
axioms its members reach, which is the set `collect` finds from any of them. -/
partial def axVisit (env : Environment) (v : Name) : StateM AxState Unit := do
  let i := (← get).next
  modify fun s => { s with next := i + 1, index := s.index.insert v i, low := s.low.insert v i,
                           stack := s.stack.push v, onStack := s.onStack.insert v }
  let (own, succ) := axEdges env v
  let mut acc := own
  for w in succ do
    let s ← get
    if let some r := s.done[w]? then
      acc := nameUnion acc r
    else if s.index.contains w then
      -- `w` is on the stack: same component as `v`.
      modify fun s => { s with low := s.low.insert v (min (s.low.getD v i) (s.index.getD w i)) }
    else
      axVisit env w
      let s ← get
      if let some r := s.done[w]? then
        acc := nameUnion acc r
      else
        modify fun s => { s with low := s.low.insert v (min (s.low.getD v i) (s.low.getD w i)) }
  modify fun s => { s with acc := s.acc.insert v acc }
  let s ← get
  if s.low.getD v i == i then
    -- `v` is the root of a component: pop its members, give each the union.
    let rec pop (members : Array Name) (all : Std.HashSet Name) :
        StateM AxState (Array Name × Std.HashSet Name) := do
      let s ← get
      let some w := s.stack.back? | return (members, all)
      modify fun s => { s with stack := s.stack.pop, onStack := s.onStack.erase w }
      let all := nameUnion all (s.acc.getD w {})
      if w == v then return (members.push w, all) else pop (members.push w) all
    let (members, all) ← pop #[] {}
    modify fun s => members.foldl (fun s m => { s with done := s.done.insert m all,
                                                       acc := s.acc.erase m }) s

/-- The axioms that `n` depends on, as `#print axioms` reports them, from the
state `st` that earlier calls filled. -/
def axiomsOf (env : Environment) (st : IO.Ref AxState) (n : Name) : IO (Array Name) := do
  let s ← st.get
  let s := if s.done.contains n then s else (axVisit env n).run s |>.2
  st.set s
  return (s.done.getD n {}).toArray

/-- Declarations of many modules, from one environment: the modules are
imported once, so a large target does not pay the import cost per module.
`pairs` are (module, file). -/
def cmdDecls (pairs : List (String × String)) : IO Unit := do
  let env ← importModules (pairs.toArray.map fun (m, _) => { module := m.toName }) {}
    (loadExts := true)
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let axSt ← IO.mkRef ({} : AxState)
  -- Declarations grouped by module index, in one pass over the environment.
  let mut byIdx : Std.HashMap Nat (Array (Name × ConstantInfo)) := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if let some idx := env.getModuleIdxFor? n then
      byIdx := byIdx.insert idx.toNat ((byIdx.getD idx.toNat #[]).push (n, ci))
  for (module, file) in pairs do
    let some idx := env.getModuleIdx? module.toName
      | throw <| IO.userError s!"module {module} is not in the environment"
    let src ← IO.FS.readFile file
    let bytes := src.toUTF8
    let ictx := Parser.mkInputContext src file
    for (n, ci) in byIdx.getD idx.toNat #[] do
      let some ranges := declRangeExt.find? env n | continue
      let (stx, _, _) := Parser.parseCommand ictx pmctx
        { pos := ictx.fileMap.ofPosition ranges.range.pos } {}
      let some (sig, body) := regions stx | continue
      -- Keep only a constant that the parsed command declares: its `declId` is a
      -- suffix of the constant's name, or the command has no `declId` (an
      -- anonymous `instance`). A compiler-generated constant (from `deriving`)
      -- has a range inside another command, and Lean versions differ in which
      -- ones they generate, so it is not part of the certificate.
      let written := (firstOfKinds [``Parser.Command.declId] stx).bind fun d =>
        (d.getArgs.find? (·.isIdent)).map (·.getId)
      if let some w := written then
        unless w.components.isSuffixOf n.components do continue
      let axioms ← axiomsOf env axSt n
      emit <| Json.mkObj
        [("name", toJson n.toString), ("module", toJson module),
         ("kind", toJson (kindOf env n ci)),
         ("statement", toJson (textOf bytes sig)), ("statementRange", rangeJson sig),
         ("body", toJson (textOf bytes body)), ("bodyRange", rangeJson body),
         ("axioms", toJson (axioms.map (·.toString)))]

/-- `decls-batch <list>`: each line of `<list>` is `module<TAB>file`. -/
def cmdDeclsBatch (list : String) : IO Unit := do
  let lines := (← IO.FS.readFile list).splitOn "\n" |>.filter (· ≠ "")
  let pairs ← lines.mapM fun l => match l.splitOn "\t" with
    | [m, f] => pure (m, f)
    | _ => throw <| IO.userError s!"decls-batch: bad line '{l}'"
  cmdDecls pairs

def cmdDeprecated (modules : List String) : IO Unit := do
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {}
    (loadExts := true)
  for (n, _) in env.constants.toList do
    if let some e := Linter.deprecatedAttr.getParam? env n then
      emit <| Json.mkObj
        [("name", toJson n.toString),
         ("newName", toJson (e.newName?.map (·.toString)))]

/-- One request's held import, for `serve`'s cache: the import names
`headerImports` computed, and the environment they built. -/
structure ServeCache where
  imports : Array Name
  env : Environment

/-- `serve`: one request per line of stdin, `{"file", "offsets"}`; one reply
per line of stdout, `{"regions", "nodes"}` — `regionsArray` over the whole
file, and `nodeAt` at each of `offsets`, from one import kept across requests
(`docs/parallel.md` C1). The import is rebuilt only when a request's file has
a different header than the one the cache holds (C2); the same module's
requests, with the same imports, all answer from the kept import (C3). Ends
at end of file on stdin. -/
partial def cmdServe : IO Unit := do
  let stdin ← IO.getStdin
  let cacheRef ← IO.mkRef (none : Option ServeCache)
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    let line := line.trimAscii.toString
    if line.isEmpty then loop else
    let req ← match Json.parse line with
      | .ok j => pure j
      | .error e => throw <| IO.userError s!"serve: bad request: {e}"
    let file : String ← match req.getObjValAs? String "file" with
      | .ok f => pure f
      | .error e => throw <| IO.userError s!"serve: {e}"
    let offsets : List Nat := (req.getObjValAs? (List Nat) "offsets").toOption.getD []
    let src ← IO.FS.readFile file
    let bytes := src.toUTF8
    let ictx := Parser.mkInputContext src file
    let (hdr, st0, msgs0) ← Parser.parseHeader ictx
    let imports := headerImports hdr.raw
    let cached ← cacheRef.get
    let env ← match cached with
      | some c =>
        if c.imports == imports then pure c.env
        else do
          let env ← importModules (imports.map fun n => { module := n }) {} (loadExts := true)
          cacheRef.set (some { imports, env })
          pure env
      | none => do
          let env ← importModules (imports.map fun n => { module := n }) {} (loadExts := true)
          cacheRef.set (some { imports, env })
          pure env
    let pmctx : Parser.ParserModuleContext := { env, options := {} }
    let regions ← regionsArray ictx pmctx st0 msgs0
    let nodes ← offsets.toArray.mapM (nodeAt ictx pmctx st0 msgs0 file bytes)
    emit <| Json.mkObj [("regions", Json.arr regions), ("nodes", Json.arr nodes)]
    loop
  loop

end LeanMendProbe

open LeanMendProbe in
unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  match args with
  | "imports" :: files => cmdImports files
  | ["decls", m, f] => cmdDecls [(m, f)]
  | ["decls-batch", l] => cmdDeclsBatch l
  | ["regions", f] => cmdRegions f
  | "node" :: f :: os => cmdNode f (os.map String.toNat!)
  | "deprecated" :: ms => cmdDeprecated ms
  | ["serve"] => cmdServe
  | _ =>
    IO.eprintln "usage: imports <file>… | decls <module> <file> | decls-batch <list> | regions <file> | node <file> <offset>… | deprecated <module>… | serve"
    return 2
  return 0
