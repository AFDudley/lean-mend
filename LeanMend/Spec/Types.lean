/-!
# Operands

The typed operands of the machine. See `docs/machine.md` § Operands and
`docs/glossary.md`. The shell parses raw input into these types once, at the
edge (concept B2). This module has no IO.
-/

namespace LeanMend

/-- A Lean release, as written in `lean-toolchain`. -/
structure Toolchain where
  name : String
  deriving DecidableEq, Repr

/-- The kind of a declaration, as the probe reports it. -/
inductive DeclKind where
  | «theorem» | «def» | «instance» | «abbrev» | «axiom»
  | «inductive» | «structure» | «class»
  | other
  deriving DecidableEq, Repr

/-- A declaration that defines a type. Its fields or constructors are its
statement and it has no body. lean-mend records it but never edits it, except
with `--annotate-binders` (decision D11). -/
def DeclKind.isType : DeclKind → Bool
  | .inductive | .structure | .class => true
  | _ => false

/-- A definition change can change what the target computes (`docs/glossary.md`). -/
def DeclKind.computes : DeclKind → Bool
  | .def | .instance | .abbrev => true
  | _ => false

/-- One declaration in a certificate. -/
structure Decl where
  name : String
  module : String
  kind : DeclKind
  /-- SHA-256 of the statement region, after the alias map. -/
  statementHash : String
  /-- SHA-256 of the body region. -/
  bodyHash : String
  axioms : List String
  deriving DecidableEq, Repr

/-- A record of a target at one toolchain (`docs/verification.md`). -/
structure Certificate where
  toolchain : Toolchain
  built : List String
  decls : List Decl
  deriving Repr

/-- Old name to final new name, from `@[deprecated]` under the new toolchain. -/
structure AliasMap where
  pairs : List (String × String)
  deriving Repr

/-- The name a baseline declaration has after the alias map. -/
def AliasMap.rename (m : AliasMap) (n : String) : String :=
  (m.pairs.lookup n).getD n

/-- The error classes. The type is closed: a new class is a change here, and
the type checker then finds every function that must handle it (concept B4). -/
inductive ErrorClass where
  | unknownIdentifier
  | unknownNamespace
  | missingDecidable
  | typeMismatch
  | simpNoProgress
  | unsolvedGoals
  /-- A binder without a type repeats a section `variable`'s name, which Lean
  v4.33 reads as a forbidden change of that variable's binder kind ("Only
  parameters appearing in the declaration header may have their binders kinds
  be overridden"). -/
  | binderOverride
  /-- A tactic ran after its goal was closed ("No goals to be solved"). -/
  | noGoals
  | heartbeat
  | wallclock
  | unknown
  deriving DecidableEq, Repr

inductive Severity where
  | error | warning | information
  deriving DecidableEq, Repr

/-- One message from `lean --json`. Raw input, parsed once. -/
structure Diagnostic where
  module : String
  line : Nat
  column : Nat
  endLine : Nat
  endColumn : Nat
  severity : Severity
  /-- Lean's message kind, for example `lean.unknownIdentifier._namedError`.
  `[anonymous]` when Lean names none. -/
  kind : String
  text : String
  deriving Repr

/-- The part of a declaration a site is in (`docs/glossary.md`). -/
inductive SiteRegion where
  | statement | body
  deriving DecidableEq, Repr

/-- A failing position, with the syntax node the probe found for it. -/
structure Site where
  diagnostic : Diagnostic
  /-- The declaration that contains the site, when the probe has read the
  file's regions. An alias rename needs no declaration. -/
  decl : Option String
  /-- The region of `decl` that holds the site's start, when known. -/
  region : Option SiteRegion
  /-- Byte offset where `decl`'s command starts, when known. -/
  declStart : Option Nat
  /-- The source text of `[start, stop)`. -/
  text : String := ""
  /-- Byte offset and text of `decl`'s body region, when known. -/
  body : Option (Nat × String) := none
  /-- Byte offset and text of `decl`'s statement region, when known. For a
  type, the whole command. -/
  statement : Option (Nat × String) := none
  /-- Byte range of the smallest syntax node that contains the error. -/
  start : Nat
  stop : Nat
  deriving Repr

inductive Entrenchment where
  | derived | ratified | proposed
  deriving DecidableEq, Repr

/-- Where an edit may go. There is no constructor for a statement region, so an
edit to a statement cannot be built (decision D5, concept B1). -/
inductive EditTarget where
  /-- Inside the body region of the named declaration. -/
  | body (decl : String)
  /-- Replace a deprecated name by its alias target, anywhere. -/
  | aliasRename (old new : String)
  /-- Add a type to a binder group in a statement: `{σ σ'}` becomes
  `{σ σ' : _}`. The one statement edit, applied only with
  `--annotate-binders` (decision D11). -/
  | typeAnnotation (decl : String)
  /-- Insert text before the named declaration's command, for example
  `set_option maxHeartbeats N in`. Outside the statement region. -/
  | beforeDecl (decl : String)
  deriving Repr

/-- One edit that a rule proposes for one site. -/
structure Candidate where
  rule : String
  entrenchment : Entrenchment
  target : EditTarget
  start : Nat
  stop : Nat
  replacement : String
  /-- The atoms and identifiers of the parsed replacement, from the probe. -/
  tokens : List String
  deriving Repr

/-- Tokens a candidate may not add (`docs/verification.md`, structural checks). -/
def forbiddenTokens : List String :=
  ["sorry", "admit", "axiom", "native_decide", "implemented_by", "extern",
   "unsafe", "opaque",
   -- decision D10: a candidate never adds a declaration
   "def", "theorem", "lemma", "instance", "abbrev", "inductive", "structure",
   "class", "example", "mutual", "attribute"]

/-- The structural check on a candidate's syntax. -/
def Candidate.clean (c : Candidate) : Bool :=
  c.tokens.all (fun t => !forbiddenTokens.contains t)

/-- An accepted patch. It cannot be built without its evidence (concept D4). -/
structure Accepted where
  candidate : Candidate
  errorsBefore : Nat
  errorsAfter : Nat
  fell : errorsAfter < errorsBefore
  clean : candidate.clean = true
  /-- Linter warnings inside the replaced bytes, after the edit. -/
  lintAtEdit : Nat
  lintFree : lintAtEdit = 0

/-- Card kinds (`docs/verification.md`). -/
inductive CardKind where
  | behavior | violation | spec | decision | held
  deriving DecidableEq, Repr

inductive Answer where
  | accept | reject
  deriving DecidableEq, Repr

/-- A judgment a person made on a card (concept C6). -/
structure Judgment where
  card : String
  kind : CardKind
  /-- The declaration or rule the card is about. -/
  subject : String
  answer : Answer
  author : String
  at_ : String
  deriving DecidableEq, Repr

/-- Why a transition cannot advance (concept B5). -/
inductive Refusal where
  | baselineRed (modules : List String)
  | aliasCycle (name : String)
  | dependencyRed (pkg : String)
  | hostTimeout (module : String)
  | observationMismatch (detail : String)
  | invariantBroken (module : String)
  | unknownCard (card : String)
  deriving Repr

/-- The tactic families a rule can name (`docs/rules.md`, `node`). Membership
is by the node's first token, which is stable across toolchains. -/
inductive TacticFamily where
  | simp | rw | exact | decide | any
  deriving DecidableEq, Repr

/-- The edit operations (`docs/rules.md` § Edit operations). Closed: a new
operation is a change here, and every function over candidates must handle it. -/
inductive EditOp where
  | rename (old new : String)
  /-- A namespace move with no `@[deprecated]` aliases: an identifier at the
  site that starts with the name `old` (whole components) gets `new` in its
  place. -/
  | renamePrefix (old new : String)
  | simpArgAdd (lemma : String)
  | simpaToExact
  | keywordSwap (from_ to : String)
  | deleteTactic
  /-- In declaration `decl`, replace the text `old` with `new`. `old` must
  occur exactly once in the declaration's body. The form in which an agent or a
  person returns a residue repair (`docs/rules.md` § From residue to rule). -/
  | replaceInBody (decl old new : String)
  /-- `match x with | p => a | _ => b`, where `p` binds no variable, becomes
  `if x = p then a else b`. -/
  | matchToIf
  /-- `match x with` whose patterns are all numerals or `_` becomes
  `match x.val with`: the same arms, over the wrapped natural number. -/
  | matchOnVal
  /-- Insert `tactic` after the node, on its own line at the node's column:
  close a goal that the node leaves open. -/
  | appendTactic (tactic : String)
  | heartbeats (n : Nat)
  deriving DecidableEq, Repr

/-- A ratified or proposed rule, parsed from `rules/*.json`. -/
structure Rule where
  name : String
  cls : ErrorClass
  entrenchment : Entrenchment
  family : TacticFamily
  ops : List EditOp
  deriving Repr

/-- One token of a syntax node, from the probe's `node`. -/
structure Token where
  text : String
  start : Nat
  stop : Nat
  deriving Repr

/-- One syntax node that contains a site, from the probe's `node`. -/
structure Node where
  kind : String
  start : Nat
  stop : Nat
  /-- The node's source text. -/
  text : String
  /-- The node's column (code points from the start of its line). -/
  column : Nat
  tokens : List Token
  deriving Repr

end LeanMend
