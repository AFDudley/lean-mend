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
  /-- `String.hash` of the statement's token sequence, after the alias map
  (`docs/verification.md` § The certificate). -/
  statementHash : String
  /-- `String.hash` of the body region's text, after the alias map. -/
  bodyHash : String
  axioms : List String
  deriving DecidableEq, Repr

/-- A record of a target at one toolchain (`docs/verification.md`). -/
structure Certificate where
  toolchain : Toolchain
  built : List String
  decls : List Decl
  /-- Declarations whose statement lean-mend changed to follow a definition
  change, under `--follow-definition-changes` (decision D12). Empty in a
  baseline. -/
  followed : List String := []
  deriving Repr

/-- A declaration that the certificate selects but whose row the probe cannot
give (`docs/verification.md` § The certificate). `compare` would not check a
declaration with no row, so the run stops on it. -/
structure DeclUnread where
  module : String
  decl : String
  /-- The probe's reason, for example the byte where the declaration starts
  and no command that parsed holds it. -/
  reason : String
  deriving DecidableEq, Repr

def DeclUnread.message (e : DeclUnread) : String :=
  s!"lean-mend: the certificate has no row for {e.decl} in {e.module}: {e.reason}"

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
  /-- A tactic could not act on its goal ("Tactic `split` failed: …", "omega
  could not prove the goal: …"). -/
  | tacticFailed
  /-- A tactic ran after its goal was closed ("No goals to be solved"). -/
  | noGoals
  | heartbeat
  | wallclock
  /-- A declaration picked up an axiom at the new toolchain that it did not
  have at the old one (`docs/verification.md` § The cause, `Change.added`).
  Not from `classify`: `classifyCause` answers it from an `AxiomCause`
  (decision D13, `docs/rules.md` § Axiom-finding rules). -/
  | axiomsAdded
  /-- The old-toolchain counterpart of `axiomsAdded` (`Change.removed`). -/
  | axiomsRemoved
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
  /-- The whole text of the site's file. -/
  file : String := ""
  /-- Byte offset and text of `decl`'s whole command, when known. -/
  declText : Option (Nat × String) := none
  /-- Byte offset and text of `decl`'s statement region, when known. For a
  type, the whole command. -/
  statement : Option (Nat × String) := none
  /-- Byte range of the smallest syntax node that contains the error. -/
  start : Nat
  stop : Nat
  /-- `decl`'s index among the module's declarations, in source order
  (`docs/parallel.md` X1). `0` when the declaration is not known. -/
  declIndex : Nat := 0
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
  /-- Inside a statement: the same `match` edit that lean-mend already made in
  a declaration body this run, so the statement stays about the same thing.
  Applied only with `--follow-definition-changes` (decision D12). -/
  | followStatement (decl : String)
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
  /-- The identifier runs that the edit adds: in the replacement and not in the
  bytes `[start, stop)` it replaces, counted with multiplicity (`addedTokens`). -/
  tokens : List String
  /-- The byte spans the edit changed, in the new text, when the edit touches
  only parts of `[start, stop)` (a file-wide rename). Empty means the whole
  replacement. The linter check counts warnings only inside these spans. -/
  changed : List (Nat × Nat) := []
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

/-- How far a site's error lies from the end of its declaration, in bytes. An
edit changes no byte after itself, so an error that it exposes later in the
same declaration has a smaller reach (`docs/machine.md` § Termination). `0`
when the declaration is not known. -/
def Site.reach (s : Site) : Nat :=
  match s.declText with
  | some (a, t) => a + t.utf8ByteSize - s.start
  | none => 0

/-- A site's AST coordinate (`docs/parallel.md` X1): its declaration's index
in source order, then its `reach`. -/
def Site.key (s : Site) : Nat × Nat := (s.declIndex, s.reach)

/-- `x` orders before `y`: a smaller declaration index, or the same
declaration index and a larger reach (farther from the declaration's end, so
earlier in it). This is a strict total order on `Nat × Nat`
(`keyLt_irrefl`, `keyLt_trans`, `keyLt_total`). -/
def keyLt (x y : Nat × Nat) : Bool :=
  decide (x.1 < y.1) || (decide (x.1 = y.1) && decide (y.2 < x.2))

theorem keyLt_iff (x y : Nat × Nat) :
    keyLt x y = true ↔ x.1 < y.1 ∨ (x.1 = y.1 ∧ y.2 < x.2) := by
  unfold keyLt; simp [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem keyLt_irrefl (x : Nat × Nat) : ¬ keyLt x x = true := by
  rw [keyLt_iff]; omega

theorem keyLt_asymm {x y : Nat × Nat} (h : keyLt x y = true) : ¬ keyLt y x = true := by
  intro h'; rw [keyLt_iff] at h h'; omega

theorem keyLt_trans {x y z : Nat × Nat} (hxy : keyLt x y = true) (hyz : keyLt y z = true) :
    keyLt x z = true := by
  rw [keyLt_iff] at hxy hyz ⊢; omega

/-- Trichotomy: any two keys compare one way, the other way, or are equal. -/
theorem keyLt_total (x y : Nat × Nat) : keyLt x y = true ∨ keyLt y x = true ∨ x = y := by
  simp only [keyLt_iff]
  obtain ⟨a1, a2⟩ := x
  obtain ⟨b1, b2⟩ := y
  simp only [Prod.mk.injEq]
  omega

/-- `a`'s position is strictly before `b`'s (`docs/parallel.md` X1, X2). -/
def Site.earlier (a b : Site) : Bool := keyLt a.key b.key

theorem Site.earlier_irrefl (a : Site) : ¬ a.earlier a = true := keyLt_irrefl a.key

theorem Site.earlier_asymm {a b : Site} (h : a.earlier b = true) : ¬ b.earlier a = true :=
  keyLt_asymm h

theorem Site.earlier_trans {a b c : Site} (hab : a.earlier b = true) (hbc : b.earlier c = true) :
    a.earlier c = true := keyLt_trans hab hbc

theorem Site.earlier_total (a b : Site) :
    a.earlier b = true ∨ b.earlier a = true ∨ a.key = b.key := keyLt_total a.key b.key

/-- `earlier`'s second argument depends only on its key: a site that ties
`b`'s key is interchangeable with `b` on the right. -/
theorem Site.earlier_congr_right {a b c : Site} (h : b.key = c.key) :
    a.earlier b = a.earlier c := by unfold Site.earlier; rw [h]

/-- An accepted patch. It cannot be built without its evidence (concept D4). -/
structure Accepted where
  candidate : Candidate
  errorsBefore : Nat
  errorsAfter : Nat
  /-- The attempted site's declaration index, and the head site's declaration
  index after the edit (`docs/parallel.md` X1). -/
  declIndexBefore : Nat
  declIndexAfter : Nat
  /-- `Site.reach` of the attempted site, and of the head site after the edit. -/
  reachBefore : Nat
  reachAfter : Nat
  /-- The earliest open position moved strictly toward the end of the file
  (`docs/parallel.md` X3): a later declaration, or the same declaration and a
  smaller reach. -/
  progress : declIndexBefore < declIndexAfter ∨
    (declIndexBefore = declIndexAfter ∧ reachAfter < reachBefore)
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
  /-- `simpArgAdd lemma` on the simp-family tactic that comes last before the
  site's own tactic, in the indented tactic sequence that holds the site. The
  site's tactic fails because that simp left a term which it no longer
  reduces (EquiVM `TransientPackedStorage` 59: `simp only [bind,
  Option.bind]` leaves `match pure x, f with …`, so a later `apply` fails). -/
  | simpArgAddPrior (lemma : String)
  | simpaToExact
  /-- `simpa [L] using h` (h a hypothesis name, which is atomic) becomes
  `simp [L] at h ⊢` then `exact h`; `simpa [L] using T` (T a term, a dotted
  name such as `hwf.d3` included) becomes `have := T`, then
  `simp [L] at this ⊢`, then `exact this`. `exact` accepts the two sides up to definitional equality, so a
  hidden difference that `simpa` rejects, such as two different `Decidable`
  instances in an `if` or a sum of literals against one literal, no longer
  blocks the proof. -/
  | simpaSplit
  /-- `simpa [L] using T` becomes `simpa [L] using! T`. Lean v4.33 closes
  `simpa … using` at reducible transparency; `using!` closes at default
  transparency, as `simpa … using` did at v4.29. -/
  | simpaUsingBang
  /-- `simpaUsingBang` on the site's `simpa` and on every `simpa … using`
  that holds it, in one edit over the outermost of them. While a `by` block in
  a `simpa` term fails, Lean does not report the outer `simpa`'s own close.
  After the inner repair it does, at an earlier position, so the inner edit
  alone is rejected (EquiVM `ERC6909.SetOperator` 49). -/
  | simpaUsingBangNested
  | keywordSwap (from_ to : String)
  | deleteTactic
  /-- Delete a `rw [show a = b by t, …]` (`rw`, `rewrite` or `erw`) whose
  every rewrite rule is a `show` term: a local equation that only changes the
  form of a term. The simp before it already rewrites `a`, so the rewrite finds
  nothing (EquiVM `Examples.BlindAuction.Reveal.Common` 2814: `simp [M]` with
  the lemmas `u256_toNat_lit*` rewrites `(⟨32⟩ : UInt256).toNat`). A rule list
  with any other rule gives no candidate: a lemma such as `if_neg` is a step
  of the proof, and its deletion only moves the error. -/
  | deleteShowRewrite
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
  /-- The class of `matchOnVal`, declaration-wide: the variable `x` in Lean's
  message `Decidable (x = n)` is compared by value everywhere in the
  declaration. `match x with`, `x = n` and `x ≠ n` become `match x.val with`,
  `x.val = n` and `x.val ≠ n`, in one edit. -/
  | valCompare
  /-- Replace the whole bullet (`· …`) that holds the site with `· tactic`: a
  decision procedure closes what the bullet's proof no longer does. The
  least preferred repair, tried after every other rule (`docs/rules.md`). -/
  | closeBullet (tactic : String)
  /-- Insert `tactic` after the node, on its own line at the node's column:
  close a goal that the node leaves open. -/
  | appendTactic (tactic : String)
  | heartbeats (n : Nat)
  /-- Insert `set_option {name} {value} in` before the declaration: the same
  insertion point as `heartbeats`, generalized to any option
  (`docs/breaking-changes.md` B1). `heartbeats` stays, for the rule files
  that already use it; a new rule should use `setOptionBefore` instead. -/
  | setOptionBefore (name value : String)
  deriving DecidableEq, Repr

/-- What an axiom-finding rule's `causeTag` matches, against the cause
constant's own shape (`docs/rules.md` § Axiom-finding rules). -/
inductive CauseTag where
  /-- The cause constant carries Lean's `@[congr]` attribute. -/
  | congrLemma
  /-- The cause constant is a generated matcher whose uses hold
  `Nat.hasNotBit`. -/
  | matcher
  /-- Matches every cause. -/
  | any
  deriving DecidableEq, Repr

/-- A ratified or proposed rule, parsed from `rules/*.json`. -/
structure Rule where
  name : String
  cls : ErrorClass
  entrenchment : Entrenchment
  family : TacticFamily
  /-- Narrows a rule whose `cls` is `axiomsAdded` or `axiomsRemoved`: the
  loader refuses such a rule with no `causeTag` as vacuous (`docs/rules.md`
  § Axiom-finding rules). `none` for every other class. -/
  causeTag : Option CauseTag := none
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
