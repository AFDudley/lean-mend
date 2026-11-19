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
* `explain <request>` — for the findings of a run (`docs/verification.md`
  § What a card explains): the certificate rows of the named declarations,
  and every constant that the named roots reach, with its module, axioms,
  the constants it uses, and the `.olean` file of its module.
* `proofs <file> <start> <stop>…` — for each byte range, the maximal ranges
  of the terms inside it whose type is a proposition, from the info trees of
  the file's elaboration.
* `regions <file>` — each declaration command of a file: qualified name,
  command range, statement and body ranges.
* `node <file> <offset>…` — for each offset, the syntax nodes that contain it,
  innermost first, with kinds, ranges, and tokens for tactic, `open` and
  `match` nodes.
* `deprecated <module>…` — `{"name", "newName"}` for every `@[deprecated]`
  declaration in the environment of the given modules.
* `export <module>…` — one line per constant of every module the roots
  reach by import, dependencies included: its module, kind, axiom set, the
  constants it uses, and the proof-erased term of its value, in a form two
  toolchains produce comparably (`docs/static-diff.md` § 1, slice 1). No
  file: `export` reads only the already-built environment.
* `export --own <module>… -- <ownMods>` — one line per constant of the
  modules in `<ownMods>`: its module, kind, its own full axiom set
  (`axiomsOf`), and the immediate constants its `axEdges` reaches, one
  hop, not walked further (`docs/static-diff.md` § 2, propagation's own
  graph). No proof-erased body: a dependency's own body hash comes from
  the dependency diff (`export --closure`), not from this call.
* `causeTactic <file> <declStart> <constant>` — the first tactic, in
  source order, whose step adds a term that uses `constant`, as a node
  (`docs/machine.md` § The tactic inside the site). `null` when none does.
* `terms <request>` — the full (never hashed) proof-erased body of each
  constant of a bounded closure, for computational equality
  (`docs/static-diff.md` § 4, slice 5): the closure of a request's `roots`,
  expanded through an owned (target) constant always, through a
  dependency constant only when the request names it in `keepDeps`.
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
  -- `moduleNameOfFileName` throws only for that case, so the probe tests it
  -- (law LM5): any other error, such as a missing file, propagates.
  let root ← realPathNormalized (← IO.currentDir)
  let rootDir := if root.toString.endsWith "/" then root.toString else root.toString ++ "/"
  let mainModuleName ←
    if rootDir.isPrefixOf (← IO.FS.realPath file).normalize.toString then
      moduleNameOfFileName file none
    else pure `_stdin
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
    -- A `mutual` block holds several declarations: report each one, with
    -- the block's own start (decision D17: `set_option … in` before one
    -- member is a parse error, so a `beforeDecl` candidate needs the
    -- `mutual` keyword's own start, not the member's).
    let isMutual := k == ``Parser.Command.mutual
    let decls := if isMutual then nodesOfKind ``Parser.Command.declaration stx else #[stx]
    let mutualStart : Json := if isMutual then
      (byteRange stx).elim Json.null (fun r => toJson r.1) else Json.null
    for d in decls do
      if let some (sig, body) := regions d then
        let written := (firstOfKinds [``Parser.Command.declId] d).bind fun i =>
          (i.getArgs.find? (·.isIdent)).map (·.getId)
        let pre := scopes.reverse.filterMap id |>.foldl (fun acc n => acc ++ n) Name.anonymous
        let name := written.map (fun w => (pre ++ w).toString) |>.getD ""
        if let some r := byteRange d then
          acc := acc.push <| Json.mkObj
            [("name", toJson name), ("range", rangeJson r),
             ("statementRange", rangeJson sig), ("bodyRange", rangeJson body),
             ("mutualStart", mutualStart)]
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

/-- The JSON of one syntax node: kind and byte range; a tactic node (kind
under `Lean.Parser.Tactic`), an `open` node or a `match` node also carries
its tokens. `none` when `n` has no byte range. Shared by `nodeAt` and
`cmdCauseTactic`. -/
def syntaxNodeJson (bytes : ByteArray) (n : Syntax) : Option Json :=
  (byteRange n).map fun r =>
    let k := n.getKind
    let base := [("kind", toJson k.toString), ("range", rangeJson r)]
    if (`Lean.Parser.Tactic).isPrefixOf k || k == ``Parser.Command.open ||
        k == ``Parser.Term.match then
      Json.mkObj (base ++ [("tokens", Json.arr (tokens bytes n))])
    else Json.mkObj base

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
    | some stx => (pathTo stx offset).reverse.filterMap (syntaxNodeJson bytes)
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
state `st` that earlier calls filled. `st.set {}` between the read and the
write empties the ref's own cell before `axVisit` mutates `s`: while the
ref's cell still holds the same `AxState` that `s` names, every one of
`s`'s hash maps has two live references (the ref and `s`), so each
`Std.HashMap.insert` inside `axVisit` copies its backing array instead of
mutating it in place — the reference-counting cost `lean_copy_expand_array`
and `lean_del_core_other` dominated an `export` of Lean core's `Std`
(leaf frames in a gdb sample, `docs/static-diff.md` § Cost). Measured on a
Std-only `export` (76 557 constants): 2:06–2:48 wall before this line, 14 s
after, same output (`diff` of the sorted NDJSON is empty). -/
def axiomsOf (env : Environment) (st : IO.Ref AxState) (n : Name) : IO (Array Name) := do
  let s ← st.get
  st.set {}
  let s := if s.done.contains n then s else (axVisit env n).run s |>.2
  st.set s
  return (s.done.getD n {}).toArray

/-- The closure of `seeds` over `axEdges`, breadth first, each name once, in
discovery order: every seed, then everything it reaches, directly or not.
Shared by `cmdExplain`'s walk from its request's `roots` and `export
--closure`'s walk from every constant of the given modules
(`docs/static-diff.md` § 1, decision S2): one walk, not two. -/
def axClosure (env : Environment) (seeds : Array Name) : Array Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for n in seeds do
    unless seen.contains n do
      seen := seen.insert n
      queue := queue.push n
  let mut i := 0
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    let (_, succ) := axEdges env n
    for s in succ do
      unless seen.contains s do
        seen := seen.insert s
        queue := queue.push s
  return queue

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

/-- The module of constant `n` in `env`, or `""` when no module declares it. -/
def moduleOfConst (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]?.map (·.toString)).getD ""
  | none => ""

/-- Runs `x` against `env`, with no file and the default options. `export`
and `explain`'s `congr` field need no elaboration of a file, only a read of
the already-built environment. -/
def runCore {α} (env : Environment) (x : CoreM α) : IO α :=
  x.toIO' { fileName := "<probe>", fileMap := default } { env }

/-- As `runCore`, for a `MetaM` action, with the default `Meta.Context` and
`Meta.State`. -/
def runMeta {α} (env : Environment) (x : MetaM α) : IO α :=
  runCore env x.run'

/-- The names carrying Lean's `@[congr]` attribute: `theoremName` of every
registered `SimpCongrTheorem` (`docs/rules.md` § Axiom-finding rules,
`causeTag` `congrLemma`). The registry is keyed by the congruence lemma's
own target function, not by the lemma's name, so this builds the reverse
set once per probe process. -/
def congrTheoremNames (env : Environment) : IO (Std.HashSet Name) :=
  runCore env do
    let table ← Meta.getSimpCongrTheorems
    return table.lemmas.fold (init := ({} : Std.HashSet Name)) fun s _ cs =>
      cs.foldl (fun s c => s.insert c.theoremName) s

/-- `Level.succ`/`.max`/`.imax`/`.param`/`.zero` as a structural string,
stable across toolchains, with no raw metavariable id (a checked
declaration's level holds none). Part of `erasedBody`'s canonical form. -/
partial def levelText : Level → String
  | .zero => "0"
  | .succ u => s!"(succ {levelText u})"
  | .max a b => s!"(max {levelText a} {levelText b})"
  | .imax a b => s!"(imax {levelText a} {levelText b})"
  | .param n => s!"(param {n})"
  | .mvar _ => "?mvar"

/-- `BinderInfo` as a structural string. -/
def binderInfoText : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strict"
  | .instImplicit => "inst"

/-- The state `erasedBody` threads: the de Bruijn depth it is at, and the
depth it assigned to each free variable it introduced for a binder it
entered (`docs/static-diff.md` § 4 step 2). -/
structure EraseCtx where
  depth : Nat := 0
  atDepth : Std.HashMap FVarId Nat := {}

/-- The placeholder for an erased proof subterm (`docs/static-diff.md` § 4
step 2): proof irrelevance makes every proof of the same proposition
interchangeable, so no proof's own shape is part of the comparable form. -/
def erasedMark : Json := Json.str "#"

/-- The proof-erased term of `e`, as nested JSON, structural over `Expr`'s
own constructors (`docs/static-diff.md` § 1 and § 4 step 2): every subterm
whose own type is a proposition becomes `erasedMark` (`Meta.isProof`, the
same check `proofRanges` uses for term info). A bound variable is its de
Bruijn depth and a constant is its qualified name, never a numeric id:
lean4export's NDJSON format (github.com/leanprover/lean4export) numbers
every Name, Level and Expr in the order one process emits them, for one
environment's own self-consistent replay; two probe processes, one per
toolchain, build two different environments, so an id one of them assigns
is not comparable to the other's. `erasedBody` keeps NDJSON's one-record-
per-declaration shape and drops its id table, naming every subterm
directly instead. Entry into a binder uses `Meta.withLocalDecl`/
`Meta.withLetDecl`, so `Meta.isProof` sees each bound variable's real type
from the ambient `LocalContext`, the mechanism `cmdProofs` uses through
`ContextInfo.runMetaM` for one declaration's info tree; `erasedBody` instead
runs over the already-built environment, with no info tree, through
`runMeta`. `Expr.mdata` is skipped, as lean4export skips it by default. -/
partial def erasedBody (ctx : EraseCtx) (e : Expr) : MetaM Json := do
  -- A kernel term in a well-formed local context: an `isProof` error is a
  -- real error, so it propagates (law LM5), and each caller names the
  -- constant ("erasedBody of <name>").
  if ← Meta.isProof e then
    return erasedMark
  match e with
  | .fvar fvarId =>
    match ctx.atDepth[fvarId]? with
    | some d => return Json.mkObj [("bvar", toJson (ctx.depth - 1 - d))]
    | none => return Json.str "?fvar"  -- unreachable: every fvar here is `ctx`'s own
  | .bvar i => return Json.mkObj [("bvar", toJson i)]
  | .mvar _ => return Json.str "?mvar"  -- unreachable: a checked declaration holds no metavariable
  | .sort u => return Json.mkObj [("sort", toJson (levelText u))]
  | .const n us => return Json.mkObj [("const", toJson n.toString), ("us", toJson (us.map levelText))]
  | .app f a => return Json.mkObj [("app", Json.arr #[← erasedBody ctx f, ← erasedBody ctx a])]
  | .lam n ty body bi =>
    let tyj ← erasedBody ctx ty
    Meta.withLocalDecl n bi ty fun fv => do
      let ctx' := { depth := ctx.depth + 1, atDepth := ctx.atDepth.insert fv.fvarId! ctx.depth }
      let bodyj ← erasedBody ctx' (body.instantiate1 fv)
      return Json.mkObj [("lam", Json.mkObj [("bi", toJson (binderInfoText bi)), ("ty", tyj), ("body", bodyj)])]
  | .forallE n ty body bi =>
    let tyj ← erasedBody ctx ty
    Meta.withLocalDecl n bi ty fun fv => do
      let ctx' := { depth := ctx.depth + 1, atDepth := ctx.atDepth.insert fv.fvarId! ctx.depth }
      let bodyj ← erasedBody ctx' (body.instantiate1 fv)
      return Json.mkObj [("forallE", Json.mkObj [("bi", toJson (binderInfoText bi)), ("ty", tyj), ("body", bodyj)])]
  | .letE n ty val body nonDep =>
    let tyj ← erasedBody ctx ty
    let valj ← erasedBody ctx val
    Meta.withLetDecl n ty val (nondep := nonDep) fun fv => do
      let ctx' := { depth := ctx.depth + 1, atDepth := ctx.atDepth.insert fv.fvarId! ctx.depth }
      let bodyj ← erasedBody ctx' (body.instantiate1 fv)
      return Json.mkObj [("letE", Json.mkObj [("ty", tyj), ("val", valj), ("body", bodyj)])]
  | .lit (.natVal v) => return Json.mkObj [("nat", toJson (toString v))]
  | .lit (.strVal s) => return Json.mkObj [("str", toJson s)]
  | .mdata _ b => erasedBody ctx b
  | .proj typeName i s =>
    return Json.mkObj [("proj", Json.mkObj
      [("type", toJson typeName.toString), ("idx", toJson i), ("struct", ← erasedBody ctx s)])]

/-- `explain <request>`: the data that a card needs to state the cause of a
finding (`docs/verification.md` § What a card explains). `<request>` is a
JSON file: `{"modules": [[module, file]…], "rows": [name…], "roots": [name…]}`.
The probe imports the modules, then emits:

* a certificate row (the shape of `decls`) for each declaration of `rows`;
* `{"const", "module", "axioms", "uses", "axiom", "congr"}` for each
  constant that a constant of `roots` reaches over the edges of
  `axiomsOf` (`axEdges`): its module, its axioms, the constants it uses,
  whether it is an axiom, and whether it carries Lean's `@[congr]`
  attribute (`docs/rules.md` § Axiom-finding rules, `causeTag`
  `congrLemma`);
* `{"missing"}` for each root that the environment does not hold;
* `{"moduleFile", "olean"}` for the module of each of those constants: the
  `.olean` file that Lean loads it from, so the shell can name the package;
* `{"sysroot"}`: the toolchain's root directory. -/
def cmdExplain (req : String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile req) with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"explain: bad request: {e}"
  let get {α} [FromJson α] (k : String) : IO α := match j.getObjValAs? α k with
    | .ok v => pure v
    | .error e => throw <| IO.userError s!"explain: field '{k}': {e}"
  let pairs : List (List String) ← get "modules"
  let rows : List String ← get "rows"
  let roots : List String ← get "roots"
  let pairs ← pairs.mapM fun
    | [m, f] => pure (m, f)
    | _ => throw <| IO.userError "explain: a module entry is not [module, file]"
  let env ← importModules (pairs.toArray.map fun (m, _) => { module := m.toName }) {}
    (loadExts := true)
  let axSt ← IO.mkRef ({} : AxState)
  let congrNames ← congrTheoremNames env
  let keep : Std.HashSet Name := rows.foldl (fun s r => s.insert r.toName) {}
  let mut byIdx : Std.HashMap Nat (Array (Name × ConstantInfo)) := {}
  for (n, ci) in env.constants.toList do
    if keep.contains n then
      if let some idx := env.getModuleIdxFor? n then
        byIdx := byIdx.insert idx.toNat ((byIdx.getD idx.toNat #[]).push (n, ci))
  for (module, file) in pairs do
    let some idx := env.getModuleIdx? module.toName
      | throw <| IO.userError s!"module {module} is not in the environment"
    moduleRows env axSt module file (byIdx.getD idx.toNat #[])
  -- The closure of the roots, breadth first (`axClosure`).
  for r in roots do
    if (env.checked.get.find? r.toName).isNone then
      emit <| Json.mkObj [("missing", toJson r)]
  let seeds := (roots.filter fun r => (env.checked.get.find? r.toName).isSome).map (·.toName)
  let mut mods : Std.HashSet String := {}
  for n in axClosure env seeds.toArray do
    let (own, succ) := axEdges env n
    let mut uses : Array Name := #[]
    let mut local_ : Std.HashSet Name := {}
    for s in succ do
      unless local_.contains s do
        local_ := local_.insert s
        uses := uses.push s
    let module := moduleOfConst env n
    mods := mods.insert module
    emit <| Json.mkObj
      [("const", toJson n.toString), ("module", toJson module),
       ("axioms", toJson ((← axiomsOf env axSt n).map (·.toString))),
       ("uses", toJson (uses.map (·.toString))), ("axiom", toJson (own.contains n)),
       ("congr", toJson (congrNames.contains n))]
  for m in mods.toArray do
    unless m.isEmpty do
      emit <| Json.mkObj [("moduleFile", toJson m), ("olean", toJson (← findOLean m.toName).toString)]
  emit <| Json.mkObj [("sysroot", toJson (← findSysroot).toString)]

/-- `export <module>…`: one JSON line per constant of every module the
given roots reach by import, dependencies included — the whole
environment `importModules` builds, as `decls-batch` does, but with no
file: `export` needs no statement text or byte range, only the elaborated
declaration itself, so it takes module names, not `module<TAB>file`
pairs. `export --closure <module>…` (`docs/static-diff.md` § 1, decision
S2) imports the same modules, but walks the closure from every constant
whose own module is one of the given names (BFS over `axEdges`, as
`cmdExplain`'s own `roots` walk does) and emits a line for each
constant the walk reaches whose module is **not** one of the given
names: the given modules are both the import roots and, for `--closure`,
the target whose own constants are not dependencies and so are never
emitted, only walked through to reach what they use. This is the mode
the dependency diff uses (`LeanMend.Shell.DepDiff.dependencyRows`): the
given modules are every module of the target, so the walk reaches
exactly the dependency constants the target's declarations use, not
every constant the whole import closure holds (`docs/static-diff.md`
§ Cost: a full closure of Lean core, Std, Batteries and Mathlib, on
EquiVM's pins, did not fit a practical run).

Each line: `const`, `module`, `kind` (`kindOf`), `axioms` (`axiomsOf`),
`uses` (the immediate edges of `axEdges`, as `explain` reports them),
`axiom` (whether `const` is itself an axiom), and `body`: the
proof-erased term of its value (`erasedBody`), `null` for a constant
with no value (an `axiom`, or the type of an `inductive`, `structure` or
`class`), or `erasedMark` for a `theorem` without calling `erasedBody` at
all: proof irrelevance (`docs/decisions.md` D16) means a theorem's own
proof term carries no information the axiom set does not already carry,
the same reason `erasedBody` erases every proof subterm inside a `def`.
In `--closure` mode, `body` of a `def`, `instance` or `abbrev` is
`toString (hash body.compress)`, not the term itself: the dependency
diff only needs to know whether a body changed (`docs/static-diff.md`
§ 1), and a Mathlib term can be large, so comparing (and storing) a hash
avoids materializing and transmitting the full term for every unchanged
constant. A constant whose hash differs between the two toolchains is
not re-queried for its full term in this slice: nothing reads it yet
(the certifying step of `docs/static-diff.md` § 4 is not built). Two
export runs, one per toolchain (decision S1), give a comparable `body`
(or hash) for an unchanged constant: `erasedBody`'s doc comment states
why. After the constant lines: one `moduleFile`/`olean` line per module
touched, and one `sysroot` line — the same shape `cmdExplain` emits, so
the shell's dependency diff resolves each constant's owner the way
card-cause resolves one (`LeanMend.Shell.Cause.ownerOfOlean`).
`erasedBody` runs under the probe's default heartbeat budget; a failure
(including a heartbeat timeout) names the constant and stops the whole
`export` — no constant is silently skipped and no finding is silently
missed. -/
def cmdExport (modules ownMods : List String) (closure : Bool) : IO Unit := do
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {}
    (loadExts := true)
  let axSt ← IO.mkRef ({} : AxState)
  let emitOne (n : Name) (ci : ConstantInfo) : IO String := do
    let (own, succ) := axEdges env n
    let mut uses : Array Name := #[]
    let mut local_ : Std.HashSet Name := {}
    for s in succ do
      unless local_.contains s do
        local_ := local_.insert s
        uses := uses.push s
    let body ← match ci with
      | .thmInfo _ => pure erasedMark
      | _ => match ci.value? (allowOpaque := true) with
        | some v =>
          let j ← try runMeta env (erasedBody {} v)
                   catch e => throw <| IO.userError s!"export: erasedBody of {n}: {e}"
          pure <| if closure then toJson (toString (hash j.compress)) else j
        | none => pure Json.null
    let module := moduleOfConst env n
    emit <| Json.mkObj
      [("const", toJson n.toString), ("module", toJson module),
       ("kind", toJson (kindOf env n ci)),
       ("axioms", toJson ((← axiomsOf env axSt n).map (·.toString))),
       ("uses", toJson (uses.map (·.toString))),
       ("axiom", toJson (own.contains n)),
       ("body", body)]
    pure module
  let mut mods : Std.HashSet String := {}
  if closure then
    let ownSet : Std.HashSet String := ownMods.foldl (fun s m => s.insert m) {}
    let seeds := (env.constants.toList.filterMap fun (n, _) =>
      if !n.isInternal && ownSet.contains (moduleOfConst env n) then some n else none).toArray
    for n in axClosure env seeds do
      unless ownSet.contains (moduleOfConst env n) do
        let some ci := env.checked.get.find? n | continue
        mods := mods.insert (← emitOne n ci)
  else
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      if (env.getModuleIdxFor? n).isNone then continue
      mods := mods.insert (← emitOne n ci)
  for m in mods.toArray do
    unless m.isEmpty do
      emit <| Json.mkObj [("moduleFile", toJson m), ("olean", toJson (← findOLean m.toName).toString)]
  emit <| Json.mkObj [("sysroot", toJson (← findSysroot).toString)]

/-- `export --own <module>… -- <ownMods>` (`docs/static-diff.md` § 2):
propagation's own graph. One line per constant whose own module is in
`<ownMods>` (the target's own built modules): `const`, `module`, `kind`
(`kindOf`), `uses` (the immediate edges of `axEdges`, one hop, not
walked further — a dependency constant's own axioms and body hash come
from the dependency diff, `export --closure`, not from here), and
`axioms` (`axiomsOf`'s full set): propagation needs a declaration's own
full axiom set at both sides to tell a dependency reach the declaration
already had the axiom through some other path from one it does not
(`docs/static-diff.md` § 2, measured: without this, EquiVM's pins gave
over 100 000 spurious axiom predictions against 42 real ones). No
`erasedBody`: propagation does not compare an own declaration's body. -/
def cmdExportOwn (modules ownMods : List String) : IO Unit := do
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {}
    (loadExts := true)
  let axSt ← IO.mkRef ({} : AxState)
  let ownSet : Std.HashSet String := ownMods.foldl (fun s m => s.insert m) {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let module := moduleOfConst env n
    unless ownSet.contains module do continue
    let (_, succ) := axEdges env n
    let mut uses : Array Name := #[]
    let mut local_ : Std.HashSet Name := {}
    for s in succ do
      unless local_.contains s do
        local_ := local_.insert s
        uses := uses.push s
    emit <| Json.mkObj
      [("const", toJson n.toString), ("module", toJson module),
       ("kind", toJson (kindOf env n ci)), ("uses", toJson (uses.map (·.toString))),
       ("axioms", toJson ((← axiomsOf env axSt n).map (·.toString)))]
  emit <| Json.mkObj [("sysroot", toJson (← findSysroot).toString)]

/-- `export --ownClosure <module>… -- <ownMods>` (`docs/static-diff.md`
§ 3): the target's own generated auxiliaries (matchers, equation lemmas,
`deriving` output, well-founded-recursion helpers), the complement of
`--closure`'s own filter. `--closure` imports the given roots and emits
every constant the walk reaches whose module is **not** one of `ownMods`
(the dependency constants, `LeanMend.Shell.DepDiff`); `--ownClosure` keeps
exactly the opposite filter and no walk at all, over the same import:
every constant of `env.constants.toList` whose module **is** one of
`ownMods`. A generated auxiliary of a target declaration is declared in
the same module as its owner, so a direct module-membership filter
already reaches every one — unlike a dependency constant, which a target
declaration can reach many imports away, there is no walk to bound here.
The line shape is `cmdExport`'s own (`const`, `module`, `kind`, `axioms`,
`uses`, `axiom`, `body`, then one `moduleFile`/`olean` line per module and
one `sysroot` line), so `LeanMend.Shell.parseExport` reads it unchanged
with `own := {}` (nothing here is a dependency to exclude): the body is
hashed for a `def`/`instance`/`abbrev` exactly as `--closure` hashes it
(`LeanMend.Core.GenAux` only needs to know whether a body changed). -/
def cmdExportOwnFull (modules ownMods : List String) : IO Unit := do
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {}
    (loadExts := true)
  let axSt ← IO.mkRef ({} : AxState)
  let ownSet : Std.HashSet String := ownMods.foldl (fun s m => s.insert m) {}
  let emitOne (n : Name) (ci : ConstantInfo) : IO String := do
    let (own, succ) := axEdges env n
    let mut uses : Array Name := #[]
    let mut local_ : Std.HashSet Name := {}
    for s in succ do
      unless local_.contains s do
        local_ := local_.insert s
        uses := uses.push s
    let body ← match ci with
      | .thmInfo _ => pure erasedMark
      | _ => match ci.value? (allowOpaque := true) with
        | some v =>
          let j ← try runMeta env (erasedBody {} v)
                   catch e => throw <| IO.userError s!"export --ownClosure: erasedBody of {n}: {e}"
          pure <| toJson (toString (hash j.compress))
        | none => pure Json.null
    let module := moduleOfConst env n
    emit <| Json.mkObj
      [("const", toJson n.toString), ("module", toJson module),
       ("kind", toJson (kindOf env n ci)),
       ("axioms", toJson ((← axiomsOf env axSt n).map (·.toString))),
       ("uses", toJson (uses.map (·.toString))),
       ("axiom", toJson (own.contains n)),
       ("body", body)]
    pure module
  let mut mods : Std.HashSet String := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if ownSet.contains (moduleOfConst env n) then
      mods := mods.insert (← emitOne n ci)
  for m in mods.toArray do
    unless m.isEmpty do
      emit <| Json.mkObj [("moduleFile", toJson m), ("olean", toJson (← findOLean m.toName).toString)]
  emit <| Json.mkObj [("sysroot", toJson (← findSysroot).toString)]

/-- The byte ranges of the proofs in `trees`: each term whose type is a
proposition, and each `by` block whose goals are propositions
(`docs/verification.md` § What a card explains). Lean records a `by` block
as tactic info with its goals, not as term info. The trees come from a file
that builds, so an error that `isProof` or `isProp` throws is a real error:
it propagates with the node's byte range (law LM5). -/
def proofRanges (trees : Array Elab.InfoTree) : IO (Array (Nat × Nat)) := do
  let mut out := #[]
  for t in trees do
    out ← t.foldInfoM (init := out) fun ctx info acc => do
      let at? := (byteRange info.stx).map fun (s, e) => s!" at bytes {s}-{e}"
      let proof ← match info with
        | .ofTermInfo ti =>
          try ti.runMetaM ctx (Meta.isProof ti.expr)
          catch e => throw <| IO.userError s!"proofs: isProof{at?.getD ""}: {e}"
        | .ofTacticInfo ti =>
          if ti.stx.getKind != ``Parser.Term.byTactic || ti.goalsBefore.isEmpty then pure false else
          try
            ({ ctx with mctx := ti.mctxBefore } : Elab.ContextInfo).runMetaM {} do
              ti.goalsBefore.allM fun g => do
                let d ← g.getDecl
                Meta.withLCtx d.lctx d.localInstances (Meta.isProp d.type)
          catch e => throw <| IO.userError s!"proofs: isProp of a by block's goal{at?.getD ""}: {e}"
        | _ => pure false
      let some r := byteRange info.stx | return acc
      return if proof then acc.push r else acc
  return out

/-- `proofs <file> <start> <stop>…`: elaborate the file as `lean --json`
does (`elaborate`), then emit `{"range", "proofs"}` for each pair of byte
offsets: the maximal proof ranges (`proofRanges`) inside that range. A range
that holds no proof gives an empty list. -/
def cmdProofs (file : String) (offsets : List Nat) : IO Unit := do
  let src ← IO.FS.readFile file
  let (snap, _) ← elaborate file src none
  let trees := (Language.toSnapshotTree snap).getAll.filterMap (·.infoTree?)
  let all ← proofRanges trees
  let rec pairsOf : List Nat → List (Nat × Nat)
    | a :: b :: rest => (a, b) :: pairsOf rest
    | _ => []
  for (a, b) in pairsOf offsets do
    let inside := all.filter fun (s, e) => a ≤ s && e ≤ b
    let maximal := inside.filter fun (s, e) =>
      !inside.any fun (s', e') => s' ≤ s && e ≤ e' && (s', e') != (s, e)
    let sorted := maximal.toList.eraseDups.toArray.qsort (fun x y => x.1 < y.1)
    emit <| Json.mkObj [("range", rangeJson (a, b)), ("proofs", Json.arr (sorted.map rangeJson))]

/-- The constants of the term that tactic step `ti` adds to the proof
(`docs/machine.md` § The tactic inside the site): the union, over every
goal `ti` had before it ran, of the constants of that goal's assignment in
`ti.mctxAfter`. A goal the step did not close (no assignment, for example
`intro`) adds none. -/
def tacticUses (ti : Elab.TacticInfo) : Array Name :=
  ti.goalsBefore.foldl (init := (#[] : Array Name)) fun acc g =>
    match ti.mctxAfter.getExprAssignmentExp g with
    | some e => acc ++ e.getUsedConstants
    | none => acc

/-- `causeTactic <file> <declStart> <constant>` (`docs/machine.md` § The
tactic inside the site; `docs/rules.md` § Axiom-finding rules): the first
tactic, in source order, whose step adds a term that uses `constant`
(`tacticUses`). Elaborates the file as `proofs` does (`elaborate`), finds
the command that holds byte `declStart` (a declaration's own start, or a
`mutual`'s, decision D17), and walks its info trees' `TacticInfo` nodes
inside that command's range, in the `foldInfoM` order `proofRanges` already
uses. A tactic node is a syntax node under `Lean.Parser.Tactic`, the same
test `syntaxNodeJson` uses; this excludes the enclosing `by` block
(`Parser.Term.byTactic`), whose own assigned term is the declaration's
whole proof and so always "uses" every constant the proof reaches, which
would make it win every search ahead of the real tactic that caused it. The
reply is `{"file", "declStart", "constant", "node"}`: `node` is
`syntaxNodeJson` of the first matching tactic, or `null` when no tactic of
the declaration uses `constant` — the same no-candidate rule an empty
`node` list already follows. -/
def cmdCauseTactic (file : String) (declStart : Nat) (constant : String) : IO Unit := do
  let src ← IO.FS.readFile file
  let (snap, _) ← elaborate file src none
  let cmds ← elabCommands file snap
  let bytes := src.toUTF8
  let inside (stx : Syntax) : Bool := match byteRange stx with
    | some (a, b) => a ≤ declStart && declStart < b
    | none => false
  let target := constant.toName
  let mut node : Option Json := none
  if let some cmd := cmds.find? inside then
    if let some (declA, declB) := byteRange cmd then
      let trees := (Language.toSnapshotTree snap).getAll.filterMap (·.infoTree?)
      let mut found : Option Syntax := none
      for t in trees do
        if found.isNone then
          found ← t.foldInfoM (init := found) fun _ info acc => do
            if acc.isSome then return acc
            let .ofTacticInfo ti := info | return acc
            unless (`Lean.Parser.Tactic).isPrefixOf ti.stx.getKind do return acc
            let some (a, b) := byteRange ti.stx | return acc
            unless declA ≤ a && b ≤ declB do return acc
            return if (tacticUses ti).contains target then some ti.stx else acc
      node := found.bind (syntaxNodeJson bytes)
  emit <| Json.mkObj [("file", toJson file), ("declStart", toJson declStart),
                       ("constant", toJson constant), ("node", node.getD Json.null)]

/-- The equations of a `def`, erased (`docs/static-diff.md` § 4, decision
S8): `Lean.Meta.getEqnsFor?`'s equation theorem names, each one's
telescoped pattern side (`lhs`) and value side (`rhs`), proofs erased the
same way a value's are (`erasedBody`). `none` for a constant with no
usable equations: not a `def` (`ci.defnInfo`), a `def` the equation
compiler gives none for, a `partial def` (`getEqnsFor?` itself answers
`none`: a `partial def` compiles through `Compiler.implementedByAttr`,
not the equation compiler's total-recursion path), or any equation
theorem whose own statement is not `Eq`-shaped (`Expr.eq?`): the fallback
(`LeanMend.Core.CompEq`'s `compareEquations`) needs every equation read,
or none at all, never a partial list. -/
def eqnsOfConst (env : Environment) (n : Name) (ci : ConstantInfo) : MetaM (Option (Array Json)) := do
  let .defnInfo _ := ci | return none
  let some eqNames ← Lean.Meta.getEqnsFor? n | return none
  let mut out : Array Json := #[]
  for eqName in eqNames do
    let some (.thmInfo v) := env.checked.get.find? eqName | return none
    let eqnJson : Option Json ← Meta.forallTelescope v.type (fun xs body => (do
      let some (_, lhs, rhs) := body.eq? | return none
      let atDepth : Std.HashMap FVarId Nat :=
        xs.zipIdx.foldl (fun m (fv, idx) => m.insert fv.fvarId! idx) {}
      let ctx : EraseCtx := { depth := xs.size, atDepth }
      let lhsJ ← erasedBody ctx lhs
      let rhsJ ← erasedBody ctx rhs
      pure (some (Json.mkObj [("binders", toJson xs.size), ("lhs", lhsJ), ("rhs", rhsJ)]))))
    let some j := eqnJson | return none
    out := out.push j
  return some out

/-- `terms <request>` (`docs/static-diff.md` § 4, computational equality).
`<request>` is a JSON file: `{"modules": [module…], "ownMods": [module…],
"keepDeps": [name…], "roots": [name…]}`. Imports `modules`, then walks the
closure of `roots` over `axEdges` (`axClosure`'s own edges, but not its
shared walk: this one needs a boundary `axClosure` has no concept of). A
constant owned by the target (its module in `ownMods`) is always expanded:
its own closure is what the certificate already bounds. A dependency
constant (module not in `ownMods`) is expanded only when it is in
`keepDeps` — the shell computes `keepDeps` from the already-known
dependency diff (`docs/static-diff.md` § 1): a dependency constant the
diff does not list has an unchanged hash at both sides, so the walk never
reads its body and never reaches past it, the cost rule "work over the
closure the target uses or the changed set, never the whole dependency
set" (`.scratch/static-diff-review.md`). Each line of the walk:

* `const`, `module`, `kind` (`kindOf`), `axioms`;
* `trust`: `"extern"`, `"implementedBy"`, `"opaque"`, or `null` — a stated
  trust point (decision S4), compared by name only, never by body;
* `body`: `erasedMark` for a `theorem` (proof irrelevance, decision D16),
  `null` for a constant with no value, else the full `erasedBody` term —
  never hashed, unlike `export --closure`: this command exists to give the
  structural shape `LeanMend.Core.CompEq` compares, not only whether a
  constant changed;
* `eqns`: `null` for a constant with no usable equations (`eqnsOfConst`),
  else one entry per equation lemma (`Lean.Meta.getEqnsFor?`): `binders`
  (its own universally quantified variable count), `lhs` and `rhs`, both
  `erasedBody`, with the equation's own bound variables substituted for
  the free variables `erasedBody`'s own binder cases introduce — the
  recursion-encoding fallback of `LeanMend.Core.CompEq` (decision S8).

A root the environment does not hold gets a `{"missing"}` line, as
`explain`'s roots do. After the constant lines: one `moduleFile`/`olean`
line per module touched, and one `sysroot` line, the same shape `export`
and `explain` already emit. -/
def cmdTerms (req : String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile req) with
    | .ok j => pure j
    | .error e => throw <| IO.userError s!"terms: bad request: {e}"
  let get {α} [FromJson α] (k : String) : IO α := match j.getObjValAs? α k with
    | .ok v => pure v
    | .error e => throw <| IO.userError s!"terms: field '{k}': {e}"
  let modules : List String ← get "modules"
  let ownMods : List String ← get "ownMods"
  let keepDeps : List String ← get "keepDeps"
  let roots : List String ← get "roots"
  let env ← importModules (modules.toArray.map fun m => { module := m.toName }) {}
    (loadExts := true)
  let ownSet : Std.HashSet String := ownMods.foldl (fun s m => s.insert m) {}
  let keepSet : Std.HashSet String := keepDeps.foldl (fun s n => s.insert n) {}
  let axSt ← IO.mkRef ({} : AxState)
  for r in roots do
    if (env.checked.get.find? r.toName).isNone then
      emit <| Json.mkObj [("missing", toJson r)]
  let seeds := (roots.filter fun r => (env.checked.get.find? r.toName).isSome).map (·.toName)
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for n in seeds do
    unless seen.contains n do
      seen := seen.insert n
      queue := queue.push n
  let mut mods : Std.HashSet String := {}
  let mut i := 0
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    let module := moduleOfConst env n
    if ownSet.contains module || keepSet.contains n.toString then
      let some ci := env.checked.get.find? n | continue
      let body ← match ci with
        | .thmInfo _ => pure erasedMark
        | _ => match ci.value? (allowOpaque := true) with
          | some v =>
            try runMeta env (erasedBody {} v)
            catch e => throw <| IO.userError s!"terms: erasedBody of {n}: {e}"
          | none => pure Json.null
      let trust : Option String :=
        if (Lean.Compiler.getImplementedBy? env n).isSome then some "implementedBy"
        else if Lean.isExtern env n then some "extern"
        else match ci with | .opaqueInfo _ => some "opaque" | _ => none
      let eqns ← try runMeta env (eqnsOfConst env n ci)
                 catch e => throw <| IO.userError s!"terms: eqnsOfConst {n}: {e}"
      mods := mods.insert module
      emit <| Json.mkObj
        [("const", toJson n.toString), ("module", toJson module),
         ("kind", toJson (kindOf env n ci)),
         ("axioms", toJson ((← axiomsOf env axSt n).map (·.toString))),
         ("trust", trust.map toJson |>.getD Json.null),
         ("body", body),
         ("eqns", eqns.map Json.arr |>.getD Json.null)]
      let (_, succ) := axEdges env n
      for s in succ do
        unless seen.contains s do
          seen := seen.insert s
          queue := queue.push s
  for m in mods.toArray do
    unless m.isEmpty do
      emit <| Json.mkObj [("moduleFile", toJson m), ("olean", toJson (← findOLean m.toName).toString)]
  emit <| Json.mkObj [("sysroot", toJson (← findSysroot).toString)]

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
  | ["explain", r] => cmdExplain r
  | "proofs" :: f :: os => cmdProofs f (os.map String.toNat!)
  | ["regions", f] => cmdRegions f
  | "node" :: f :: os => cmdNode f (os.map String.toNat!)
  | "deprecated" :: ms => cmdDeprecated ms
  | "export" :: "--closure" :: rest => do
    match rest.span (· ≠ "--") with
    | (roots, _ :: ownMods) => cmdExport roots ownMods true
    | _ => throw <| IO.userError "export --closure: expected '--' before the own-module list"
  | "export" :: "--own" :: rest => do
    match rest.span (· ≠ "--") with
    | (roots, _ :: ownMods) => cmdExportOwn roots ownMods
    | _ => throw <| IO.userError "export --own: expected '--' before the own-module list"
  | "export" :: "--ownClosure" :: rest => do
    match rest.span (· ≠ "--") with
    | (roots, _ :: ownMods) => cmdExportOwnFull roots ownMods
    | _ => throw <| IO.userError "export --ownClosure: expected '--' before the own-module list"
  | "export" :: ms => cmdExport ms [] false
  | ["causeTactic", f, s, c] => cmdCauseTactic f (s.toNat!) c
  | ["terms", r] => cmdTerms r
  | ["serve"] => cmdServe
  | _ =>
    IO.eprintln "usage: imports <file>… | decls <module> <file> | decls-batch <list> | explain <request> | proofs <file> <offset>… | regions <file> | node <file> <offset>… | deprecated <module>… | export [--closure|--own] <module>… [-- <ownMods>] | causeTactic <file> <declStart> <constant> | terms <request> | serve"
    return 2
  return 0
