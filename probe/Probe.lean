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
* `decls <module> <file>` — one line per declaration of `<module>` that the
  certificate selects: name, kind, statement text and statement tokens, body
  text, statement and body byte ranges, axioms. A declaration whose row the
  probe cannot give has an `unread` line with the reason. Needs the module
  built. The ranges and tokens come from the file's own commands
  (`fileCommands`).
* `decls-batch <list>` — `decls` for every `module<TAB>file` line of `<list>`,
  from one environment.
* `regions <file>` — each declaration command of a file: qualified name,
  command range, statement and body ranges.
* `node <file> <offset>…` — for each offset, the syntax nodes that contain it,
  innermost first, with kinds, ranges, and tokens for tactic, `open` and
  `match` nodes.
* `deprecated <module>…` — `{"name", "newName"}` for every `@[deprecated]`
  declaration in the environment of the given modules.
* `serve` — one JSON request per line of stdin, one JSON reply per line of
  stdout, from one long-lived process for one module (`docs/parallel.md`
  C1-C5). A `syntax` request gives `regions <file>` and
  `node <file> <offsets>…`. An `elaborate` request gives the messages of
  `lake env lean --json <file>`, and elaborates again only from the first
  command that changed since the previous request. Ends at end of file on
  stdin.

`regions` and `node` read the commands that the elaboration of the file
parsed (`elabCommands`), not a separate parse with the imports'
environment: Lean parses each command with the environment after the
command before it, so a `macro`, `syntax`, `notation` or `elab` that the file
declares parses at its later uses.
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

/-- This process's peak resident size in KiB, `VmHWM` of `/proc/self/status`
(`docs/parallel.md` P24). Each `serve` reply carries it, so the shell knows
the probe's peak when Lean stops the probe at its `lean -M` cap. -/
def peakKiB : IO Nat := do
  let st ← IO.FS.readFile "/proc/self/status"
  let words (l : String) := ((l.replace "\t" " ").splitOn " ").filter (· ≠ "")
  match (st.splitOn "\n").find? (fun l => (words l).head? == some "VmHWM:") with
  | some l => pure (((words l).getD 1 "0").toNat?.getD 0)
  | none => pure 0

/-- Emit one `serve` reply with the fields `fields` and `peakKiB`. -/
def emitReply (fields : List (String × Json)) : IO Unit := do
  emit <| Json.mkObj (fields ++ [("peakKiB", toJson (← peakKiB))])

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
statement and an empty body at its end (`docs/verification.md`). An `axiom`,
and an `opaque` with no value, has its signature as the statement and an
empty body at the signature's end. -/
def regions (stx : Syntax) : Option ((Nat × Nat) × (Nat × Nat)) := do
  if isTypeCommand stx then
    let r ← byteRange stx
    return (r, (r.2, r.2))
  let sig ← firstOfKinds [``Parser.Command.declSig, ``Parser.Command.optDeclSig] stx
  let body? := firstOfKinds
    [``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
     ``Parser.Command.whereStructInst] stx
  match body? with
  | some body =>
    let b ← byteRange body
    -- An empty signature (`abbrev T := Nat`) has no position: its statement
    -- region is the empty range where the body starts.
    pure ((byteRange sig).getD (b.1, b.1), b)
  | none =>
    let _ ← firstOfKinds [``Parser.Command.axiom, ``Parser.Command.opaque] stx
    let s ← byteRange sig
    pure (s, (s.2, s.2))

/-- The last elaboration of one file, for `serve`: the text it elaborated
and the snapshot tree that `Language.Lean.process` returned for it. The next
`elaborate` request on the same file passes the tree back, so Lean keeps the
elaborated state of every command before the first changed one
(`docs/parallel.md` C4). A `syntax` request on the same text reads the
tree's commands (`elabCommands`) and elaborates nothing. -/
structure ElabCache where
  file : String
  src : String
  snap : Language.Lean.InitialSnapshot

/-- The options of `lake env lean --json <file>` (`runFrontend`, which
`Lean.Shell` calls with no `-D` option): `Elab.async` on. One option
differs: `internal.cmdlineSnapshots` is off, as in the language server.
When it is on, Lean discards the syntax of each command after elaboration,
so it cannot find the unchanged commands of the next text, and
`elabCommands` has no syntax to read. It changes what Lean keeps, not what
Lean reports (`docs/parallel.md` C5). -/
def elabOptions : Options :=
  internal.cmdlineSnapshots.set (Elab.async.set ({} : Options) true) false

/-- The messages of one finished snapshot tree, in the order and the JSON
shape that `lean --json` prints them (`Language.SnapshotTree.runAndReport`
with no severity override): tree preorder, each unreported message, silent
messages dropped. After `maxErrors` errors, Lean prints one error "maximum
number of errors … reached, exiting" in place of the next error and stops;
so does this function. -/
def treeMessages (tree : Language.SnapshotTree) (opts : Options) : IO (Array Json) := do
  let maxE := Language.maxErrors.get opts
  let (_, _, out) ← tree.foldM (init := ((0 : Nat), false, (#[] : Array Json)))
    fun acc s => s.diagnostics.msgLog.unreported.foldlM (init := acc) fun (n, stop, out) msg => do
      if stop then return (n, stop, out)
      let n := n + (if msg.severity matches .error then 1 else 0)
      let reached := maxE != 0 && n > maxE
      let msg : Message := if reached then
        { msg with
          data := s!"maximum number of errors ({maxE}; from option `maxErrors`) reached, exiting"
          severity := .error }
        else msg
      if msg.isSilent then return (n, reached, out)
      return (n, reached, out.push (← msg.toJson))
  return out

/-- The trust level of `lean <file>` with no `--trust` option:
`Lean.defaultTrustLevel`, the believer trust level 1024 of the C++ kernel
(`LEAN_BELIEVER_TRUST_LEVEL`) plus one. `Lean.Shell` does not export it, and
the interpreter cannot call its `@[extern]` source, so the probe states it. -/
def shellTrustLevel : UInt32 := 1025

/-- Elaborate `src`, the current text of `file`, as
`lake env lean --json <file>` does (`Elab.runFrontend`): the same language
processor, main module name, trust level and options (`elabOptions`). `old?`
is the previous elaboration of the same file; Lean reuses its commands up to
the first changed one. Returns the new elaboration and its messages, in
`treeMessages` order. -/
def elaborate (file src : String) (old? : Option Language.Lean.InitialSnapshot) :
    IO (Language.Lean.InitialSnapshot × Array Json) := do
  let opts := elabOptions
  -- `Lean.Shell`: a file outside the module root gets the name `_stdin`.
  let mainModuleName ← try moduleNameOfFileName file none catch _ => pure `_stdin
  let setup (stx : Elab.HeaderSyntax) :
      Language.ProcessingT IO (Except Language.Lean.HeaderProcessedSnapshot
        Language.Lean.SetupImportsResult) :=
    pure <| .ok { imports := stx.imports, isModule := stx.isModule, mainModuleName, opts,
                  trustLevel := shellTrustLevel }
  let ctx : Language.ProcessingContext := { Parser.mkInputContext src file with }
  let snap ← Language.Lean.process setup old? ctx
  let msgs ← treeMessages (Language.toSnapshotTree snap) opts
  return (snap, msgs)

/-- The syntax of each command that the elaboration `snap` of `file` parsed,
in source order, without the end-of-file command. Lean parses each command
with the environment after the command before it, so a command that uses a
`macro`, `syntax`, `notation` or `elab` of the same file parses. A parse
with the imports' environment only does not: the parser skips such a
command, and every site in it gets no node (`tests/probe-gap.sh`). A header
that did not process (an import is missing or does not build) gives no
commands, and that is an error. -/
partial def elabCommands (file : String) (snap : Language.Lean.InitialSnapshot) :
    IO (Array Syntax) := do
  let some hp := snap.processedResult.get
    | throw <| IO.userError s!"the header of {file} did not process: an import is missing or does not build"
  let rec go (c : Language.Lean.CommandParsedSnapshot) (acc : Array Syntax) : Array Syntax :=
    let acc := if Parser.isTerminalCommand c.stx then acc else acc.push c.stx
    match c.nextCmdSnap? with
    | some t => go t.get acc
    | none => acc
  return go hp.firstCmdSnap.get #[]

/-- Every declaration command of `cmds`, the commands of one file: one JSON
object per declaration, in source order, the shape `regions <file>` emits
one per line of. Names are qualified by the enclosing `namespace` commands.
Shared by `cmdRegions` and `cmdServe`. -/
def regionsArray (cmds : Array Syntax) : Array Json := Id.run do
  -- The scope stack: `some ns` for a namespace, `none` for a section.
  let mut scopes : List (Option Name) := []
  let mut acc := #[]
  for stx in cmds do
    let k := stx.getKind
    scopes :=
      if k == ``Parser.Command.namespace then
        (stx.getArgs.find? (·.isIdent)).map (·.getId) :: scopes
      else if k == ``Parser.Command.section then none :: scopes
      else if k == ``Parser.Command.end then scopes.drop 1
      else scopes
    -- A `mutual` block holds several declarations: report each one.
    let decls := if k == ``Parser.Command.mutual then nodesOfKind ``Parser.Command.declaration stx
      else #[stx]
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
  return acc

/-- `regions <file>`: from one elaboration of the file (`elabCommands`). The
file's imports must build; the file itself may fail. -/
def cmdRegions (file : String) : IO Unit := do
  let src ← IO.FS.readFile file
  let (snap, _) ← elaborate file src none
  for j in regionsArray (← elabCommands file snap) do emit j

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

/-- The byte ranges of the atoms and identifiers of `stx`, in source order.
Whitespace and comments are not atoms, so they are in no range. -/
partial def tokenRanges (stx : Syntax) : Array (Nat × Nat) :=
  match stx with
  | .atom _ _ | .ident .. => (byteRange stx).toArray
  | _ => stx.getArgs.foldl (fun acc c => acc ++ tokenRanges c) #[]

/-- The atoms and identifiers of `stx`, in source order, with byte ranges. -/
def tokens (src : ByteArray) (stx : Syntax) : Array Json :=
  (tokenRanges stx).map fun r => Json.mkObj [("text", toJson (textOf src r)), ("range", rangeJson r)]

/-- The text of each atom and identifier of `stx` inside byte range `r`, in
source order: the statement as a token sequence (`docs/verification.md` § The
certificate). Two statements that differ only in whitespace or comments have
the same sequence. -/
def tokenTexts (src : ByteArray) (stx : Syntax) (r : Nat × Nat) : Array String :=
  (tokenRanges stx).filterMap fun (a, b) =>
    if r.1 ≤ a && b ≤ r.2 then some (textOf src (a, b)) else none

/-- The syntax nodes that contain byte offset `offset`, innermost first: kind
and byte range; tactic nodes (kind under `Lean.Parser.Tactic`) also carry
their tokens. `{"file", "offset", "nodes"}`, the shape `node <file>
<offset>…` emits one per line of. `cmds` are the commands of `file`
(`elabCommands`). Shared by `cmdNode` and `cmdServe`.

`nodes` is empty when no command contains `offset`: after a parse error, the
parser skips to the next command, and the bytes it skips are in no command.
The site at such an offset gets no node, so no rule that needs a node
proposes a candidate for it. -/
def nodeAt (cmds : Array Syntax) (file : String) (bytes : ByteArray) (offset : Nat) : Json :=
  let inside (stx : Syntax) : Bool := match byteRange stx with
    | some (a, b) => a ≤ offset && offset < b
    | none => false
  let nodes := match cmds.find? inside with
    | none => []
    | some stx => (pathTo stx offset).reverse.filterMap fun n =>
      (byteRange n).map fun r =>
        let k := n.getKind
        let base := [("kind", toJson k.toString), ("range", rangeJson r)]
        if (`Lean.Parser.Tactic).isPrefixOf k || k == ``Parser.Command.open ||
            k == ``Parser.Term.match then
          Json.mkObj (base ++ [("tokens", Json.arr (tokens bytes n))])
        else Json.mkObj base
  Json.mkObj [("file", toJson file), ("offset", toJson offset), ("nodes", Json.arr nodes.toArray)]

/-- `node <file> <offset>…`: from one elaboration of the file
(`elabCommands`), as `regions`. -/
def cmdNode (file : String) (offsets : List Nat) : IO Unit := do
  let src ← IO.FS.readFile file
  let (snap, _) ← elaborate file src none
  let cmds ← elabCommands file snap
  for offset in offsets do
    emit (nodeAt cmds file src.toUTF8 offset)

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

/-- The scope commands. They change how a later command of the same file
parses: `namespace` and `open` activate the `scoped` syntax of a namespace. -/
def scopeKinds : List SyntaxNodeKind :=
  [``Parser.Command.namespace, ``Parser.Command.section, ``Parser.Command.end,
   ``Parser.Command.open, ``Parser.Command.set_option]

/-- The commands that declare syntax and can be `local`. -/
def syntaxKinds : List SyntaxNodeKind :=
  [``Parser.Command.syntax, ``Parser.Command.macro, ``Parser.Command.notation,
   ``Parser.Command.mixfix, ``Parser.Command.elab, ``Parser.Command.binderPredicate]

/-- `cmd` has its own attribute kind `local` (`local notation …`), not one of
an attribute inside it. -/
def isLocal (cmd : Syntax) : Bool :=
  match cmd.getArgs.find? (·.getKind == ``Parser.Term.attrKind) with
  | some k => (firstOfKinds [``Parser.Term.«local»] k).isSome
  | none => false

/-- The commands of `file`, whose text is `src`, in source order, without the
end-of-file command. Each one carries `true` when its parse had an error.

Lean parses each command with the environment and the scopes after the
command before it. This function does the same from `env`, which already
holds the file's module, with no elaboration of a declaration or a proof
(`docs/verification.md` § The certificate). It elaborates two kinds of
command only:

* the scope commands (`scopeKinds`), so `namespace` and `open` activate the
  `scoped` syntax of the namespace;
* a `local` command that declares syntax (`syntaxKinds`). The module does not
  export local syntax, so `env` does not hold it. The module exports its
  other syntax, so `env` holds it from the start of the file. To elaborate
  such a command again would give each of its uses two parses.

A command of another kind that declares local syntax, for example a macro of
the file that expands to a `local notation`, is not elaborated: a later
command that uses the syntax does not parse. For a module that builds, a
parse error shows that this parse differs from Lean's, and `decls` reports
each declaration in that command as unread (`tests/cert-unread.sh`). An error
in the elaboration of a command is not checked here: its effect is a parse
error in a later command, and `decls` reports that. -/
partial def fileCommands (env : Environment) (file src : String) :
    IO (Array (Syntax × Bool)) := do
  let ictx := Parser.mkInputContext src file
  let (_, ps, _) ← Parser.parseHeader ictx
  let rec loop (acc : Array (Syntax × Bool)) : Elab.Frontend.FrontendM (Array (Syntax × Bool)) := do
    Elab.Frontend.updateCmdPos
    let st ← get
    let scope := st.commandState.scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := st.commandState.env, options := scope.opts,
        currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let (cmd, ps', msgs) := Parser.parseCommand ictx pmctx st.parserState {}
    Elab.Frontend.setParserState ps'
    if Parser.isTerminalCommand cmd then return acc
    let k := cmd.getKind
    if scopeKinds.contains k || (syntaxKinds.contains k && isLocal cmd) then
      Elab.Frontend.elabCommandAtFrontend cmd
    loop (acc.push (cmd, msgs.hasErrors))
  let (cmds, _) ← (loop #[] { inputCtx := ictx }).run
    { commandState := Elab.Command.mkState env {} {}, parserState := ps, cmdPos := ps.pos }
  return cmds

/-- `n` with a leading `_root_` removed: the name that `declId` `_root_.x`
declares is `x`. -/
def dropRoot (n : Name) : Name :=
  match n.components with
  | `_root_ :: rest => rest.foldl (· ++ ·) .anonymous
  | _ => n

/-- `stx` and, for `cmd₁ in cmd₂` (`set_option … in`, `open … in`), the
commands of `cmd₂`. -/
partial def innerCommands (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Parser.Command.in then #[stx] ++ innerCommands stx[2] else #[stx]

/-- The certificate rows of one module, from the environment `env` of the
batch and the commands of the module's file, parsed in `env`
(`fileCommands`). One JSON line per declaration that the certificate selects
(`docs/verification.md` § The certificate): the row, or an `unread` line that
names the declaration and the reason when the probe cannot give its row.

`env` holds every module of the batch, so it can hold a token that the
module's own imports do not declare: on EquiVM, `Examples.UniswapV2Pair.SpecSyntax`
imports `Stele.Notation`, which makes `this` a token, and in a batch with it
the command `def this : Expr := …` of `Examples.UniswapV2Pair.Spec` does not
parse. The shell reads a module with an `unread` line again alone
(`Shell.Target.declsOf`); a batch of one module has the module's own
environment. -/
def moduleRows (env : Environment) (axSt : IO.Ref AxState) (module file : String)
    (consts : Array (Name × ConstantInfo)) : IO Unit := do
  let src ← IO.FS.readFile file
  let bytes := src.toUTF8
  let fileMap := FileMap.ofString src
  let cmds ← fileCommands env file src
  let clean := cmds.filterMap fun (c, bad) => if bad then none else some c
  -- The nodes of the clean commands by the byte where each starts: every
  -- command, also the one after `in`, then every declaration, which wins at
  -- the same byte. Lean's declaration range of a declaration starts at the
  -- same byte as its node (`addDeclarationRanges`); a declaration that a
  -- macro command makes, such as Mathlib's `lemma`, starts at the command.
  let mut nodeAt : Std.HashMap Nat Syntax := {}
  for c in clean do
    for n in innerCommands c ++ nodesOfKind ``Parser.Command.declaration c do
      if let some (a, _) := byteRange n then nodeAt := nodeAt.insert a n
  let holds (pos : Nat) (c : Syntax) : Bool := match byteRange c with
    | some (a, b) => a ≤ pos && pos < b
    | none => false
  let unread (n : Name) (why : String) : IO Unit :=
    emit <| Json.mkObj [("name", toJson n.toString), ("module", toJson module),
                        ("unread", toJson why)]
  for (n, ci) in consts do
    let some ranges := declRangeExt.find? env n | continue
    let pos := (fileMap.ofPosition ranges.range.pos).byteIdx
    let some d := nodeAt[pos]?
      | -- A constant whose range starts inside a command that parsed, but not
        -- at a command or a declaration, is generated by that command: a
        -- constructor, a projection, a `where` function, an instance that
        -- `deriving` makes and its auxiliaries. Lean versions differ in which
        -- ones they generate, so it is not part of the certificate
        -- (`tests/cert-generated.sh`).
        if clean.any (holds pos) then continue
        unread n <| if cmds.any fun (c, bad) => bad && holds pos c then
            s!"the command that holds byte {pos}, where its declaration starts, does not parse in the probe"
          else s!"no command holds byte {pos}, where its declaration starts"
    -- Keep only a constant that the declaration declares: its `declId` is a
    -- suffix of the constant's name, or it has no `declId` (an anonymous
    -- `instance`). Another constant that starts at the same byte, such as
    -- the projection of a structure's parent, is generated.
    let written := (firstOfKinds [``Parser.Command.declId] d).bind fun i =>
      (i.getArgs.find? (·.isIdent)).map (dropRoot ·.getId)
    if let some w := written then
      unless w.components.isSuffixOf n.components do continue
    let some (sig, body) := regions d
      | -- A command that is not a declaration and has no statement region
        -- (`notation`, `deriving instance`, a macro command) generates the
        -- constant.
        if d.getKind == ``Parser.Command.declaration then
          unread n s!"the declaration at byte {pos} has no statement region"
    let axioms ← axiomsOf env axSt n
    -- `statement` is for a person to read; the certificate compares
    -- `statementTokens` (`docs/verification.md` § The certificate).
    emit <| Json.mkObj
      [("name", toJson n.toString), ("module", toJson module),
       ("kind", toJson (kindOf env n ci)),
       ("statement", toJson (textOf bytes sig)), ("statementRange", rangeJson sig),
       ("statementTokens", toJson (tokenTexts bytes d sig)),
       ("body", toJson (textOf bytes body)), ("bodyRange", rangeJson body),
       ("axioms", toJson (axioms.map (·.toString)))]

/-- Declarations of many modules, from one environment: the modules are
imported once, so a large target does not pay the import cost per module.
`pairs` are (module, file). An import of each module alone in the same
process is not an option: Lean does not free the memory of an import. On 33
EquiVM modules it reached a peak resident size of 98 GB, and the process was
killed (`docs/verification.md` § The certificate). -/
def cmdDecls (pairs : List (String × String)) : IO Unit := do
  let env ← importModules (pairs.toArray.map fun (m, _) => { module := m.toName }) {}
    (loadExts := true)
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
    moduleRows env axSt module file (byIdx.getD idx.toNat #[])

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

/-- `serve`: one request per line of stdin, one reply per line of stdout.
Ends at end of file on stdin.

* `{"op": "elaborate", "file"}` → `{"messages"}`: the messages of
  `lake env lean --json <file>` on the file's current text (C5). The
  elaboration starts again only from the first command that changed since the
  previous elaboration of the same file (C4).
* `{"op": "syntax", "file", "offsets"}` → `{"regions", "nodes"}`:
  `regionsArray` over the whole file, and `nodeAt` at each of `offsets`, from
  the commands of the file's elaboration (`elabCommands`). When the kept
  elaboration is of the same text, as after the shell's `elaborate` request
  (`Shell.Target.diagnose`), the request elaborates nothing (C1-C3); else it
  elaborates the current text first, as `elaborate` does. -/
partial def cmdServe : IO Unit := do
  let stdin ← IO.getStdin
  let elabRef ← IO.mkRef (none : Option ElabCache)
  -- Elaborate `src`, the current text of `file`, from the kept elaboration
  -- of the same file (C4), and keep the new one.
  let elabFile (file src : String) : IO (Language.Lean.InitialSnapshot × Array Json) := do
    let old? := (← elabRef.get).bind fun c => if c.file == file then some c.snap else none
    let (snap, msgs) ← elaborate file src old?
    elabRef.set (some { file, src, snap })
    return (snap, msgs)
  let rec loop : IO Unit := do
    let line ← stdin.getLine
    if line.isEmpty then return
    let line := line.trimAscii.toString
    if line.isEmpty then loop else
    let req ← match Json.parse line with
      | .ok j => pure j
      | .error e => throw <| IO.userError s!"serve: bad request: {e}"
    let field (k : String) : IO String := match req.getObjValAs? String k with
      | .ok f => pure f
      | .error e => throw <| IO.userError s!"serve: {e}"
    let file ← field "file"
    match ← field "op" with
    | "elaborate" =>
      let (_, msgs) ← elabFile file (← IO.FS.readFile file)
      emitReply [("messages", Json.arr msgs)]
    | "syntax" =>
      let offsets : List Nat := (req.getObjValAs? (List Nat) "offsets").toOption.getD []
      let src ← IO.FS.readFile file
      let kept := (← elabRef.get).bind fun c =>
        if c.file == file && c.src == src then some c.snap else none
      let snap ← match kept with
        | some s => pure s
        | none => Prod.fst <$> elabFile file src
      let cmds ← elabCommands file snap
      let bytes := src.toUTF8
      emitReply [("regions", Json.arr (regionsArray cmds)),
                 ("nodes", Json.arr (offsets.toArray.map (nodeAt cmds file bytes)))]
    | op => throw <| IO.userError s!"serve: unknown op '{op}'"
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
