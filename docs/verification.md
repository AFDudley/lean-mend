# Verification

Two questions, kept apart (concept C11):

1. Did lean-mend harm the target? This is checked on every run.
2. Is lean-mend itself correct? This is checked in lean-mend's own CI.

## 1. No harm to the target

Brief item 7. The invariant is in [machine.md](machine.md). This section says
how each part is checked, and at which assurance level (concept E1).

| Edit | Checks | Kind |
|---|---|---|
| alias rename (derived rule) | rebuild; the elaborated name is the alias target | structural + observational |
| proof edit (body of a `theorem` or `lemma`) | rebuild; structural checks; statement and axioms unchanged | structural + observational |
| `set_option maxHeartbeats` | rebuild; flagged on the report | observational |
| definition change (body of a `def`, `instance`, `abbrev`) | rebuild; structural checks; conformance; **Behavior** card | observational + judgment |
| axiom set differs | **Violation** card | judgment |

### The certificate

The probe writes a certificate for a list of modules. For each declaration:

- `name` and `kind`;
- `statement`: the source text of the statement region, for the report only;
- `statementTokens`: the atoms and identifiers of the statement region, in
  source order, each with its source text. The probe takes them from the
  syntax of the declaration command. Whitespace and comments are not tokens;
- `statementHash`: `String.hash` of the tokens, joined with one space, after
  `AliasMap.normalizeWith`;
- `type`: the elaborated type, printed with `pp.all`, for the report only;
- `axioms`: the axioms the declaration depends on, the set that
  `#print axioms` reports (the probe's `axiomsOf`, see architecture.md).
  The shell keeps them as a sorted set, and it collapses every generated
  `native_decide` axiom (`X._native.native_decide.ax_1_12`) to the one name
  `native_decide`. Lean numbers those per declaration, so their names can
  change between toolchains when the trust does not. EquiVM's certificates
  rest on them.

The certificate holds only declarations that the source declares, at both
toolchains. A constant is a row when the user wrote its name (the `declId`
of a declaration command, also of a command that a macro such as `lemma`
makes), when it is the type that a `structure`, `inductive` or `class`
command declares, or when it is an unnamed `instance`. Lean generates other
constants: the instances that `deriving BEq, Inhabited, Repr` makes and
their auxiliaries, constructors, projections, equation lemmas, `match_` and
`proof_` auxiliaries, `where` functions. None of them is a row, because
Lean versions differ in which ones they generate. `compare` has no rule
for a missing generated constant: both sides select the same set. The
selection is in § Every selected declaration has a row.

Two runs halted on a generated constant. On EVMLean,
`Ethereum.instInhabitedBlockHeader.default` exists at v4.29.0 and not at
v4.33.1. EquiVM run 9 (lean-mend 48346f7e) halted after 25441 s with
`invariantBroken` at `Stele.DiffTest.Gen`. The file is the same at v4.29.0
and at HEAD. The baseline had 33 rows and the after certificate 32: the
missing row was `Stele.DiffTest.instInhabitedPools.default`, which
`deriving Inhabited` on `Pools` makes. At v4.29.0 that constant has a
declaration range at the word `Inhabited` of the `deriving` clause. At
v4.33.1 it has no range. The probe of run 9 parsed one command at the
start of each range. At the word `Inhabited`, that parse gave the next
command, the unnamed `instance : Append Pools`. That command has no
`declId`, so the probe kept the constant, with the statement of the
instance. The selection of § Every selected declaration has a row gives
no row for it, and on the real file at v4.33.1 the probe gives 31 rows
with no `instInhabitedPools` constant. `tests/cert-generated.sh` builds
this shape: with the probe of run 9 the run halts with `invariantBroken`,
and with the current probe it ends done, both certificates with only the
declarations of the source.

An unnamed `instance` gets its name from Lean, for example
`instInhabitedPools`. The user wrote its statement, so it is a row, keyed
by that name. This is correct only if Lean gives the same name at both
toolchains. Measured on 24 unnamed instances
(`tests/fixtures/cert-generated/app/App/T.lean` and `App/Inst.lean`):
every name is the same at v4.29.0 and at v4.33.1.

| Shape | Example | Name at v4.29.0 and v4.33.1 |
|---|---|---|
| user class on a structure | `instance : Size Pools` | `instSizePools` |
| core class, `where` body | `instance : Append Pools where …` | `instAppendPools` |
| instance argument | `instance [Size α] : Size (List α)` | `instSizeList` |
| implicit argument | `instance {n : Nat} : Size (Fin n)` | `instSizeFin` |
| explicit argument | `instance (n : Nat) : OfNat Pools n` | `instOfNatPools` |
| parameterized structure | `instance [Size α] : Size (Box α)` | `instSizeBox` |
| two class arguments | `instance : HAdd Pools Nat Pools` | `instHAddPoolsNat` |
| two class arguments | `instance : Coe Nat Pools` | `instCoeNatPools` |
| function type | `instance : Size (Nat → Nat)` | `instSizeForallNat` |
| product | `instance : Size (Nat × Pools)` | `instSizeProdNatPools` |
| decidable predicate | `instance : DecidablePred IsEven` | `instDecidablePredNatIsEven` |
| decidable proposition | `instance (n : Nat) : Decidable (IsEven n)` | `instDecidableIsEven` |
| proposition with literals | `instance : Decidable (1 < 2)` | `instDecidableLtOfNat_app` |
| class on a type constructor | `instance : Functor Box` | `instFunctorBox` |
| priority | `instance (priority := low) : Inhabited Pools` | `instInhabitedPools` |
| attribute | `@[reducible] instance : Size Bool` | `instSizeBool` |
| `where` body | `instance : ToString Pools where …` | `instToStringPools` |
| applied type | `instance : Repr (Box Nat)` | `instReprBoxNat` |
| field from a `where` function | `instance : Size Tree where size := go where go …` | `instSizeTree` |
| proof field | `instance : Pos Pools where … pos _ := by omega` | `instPosPools` |
| class in `Prop` | `instance : Std.Commutative (α := Nat) (· + ·)` | `instCommutativeNatHAdd_app` |
| function type, `_app` | `instance : Inhabited (Nat → Nat)` | `instInhabitedForallNat_app` |
| section `variable` | `instance : Pos (Option α)` | `instPosOption` |
| outside a namespace | `instance : App.Inst.Size String` | `instSizeString` |

So the certificate keys an unnamed instance by its name, and it needs no
key from the source position. If a later toolchain gives an unnamed
instance another name, the baseline row has no partner in the after
certificate, and the run halts with `invariantBroken`: it stops, it does
not pass in silence. `tests/cert-generated.sh` checks all 24 names at
each bump.

Types: every `inductive`, `structure` and `class` has a row, kind `inductive`,
`structure` or `class`, whose statement is the whole command and whose body is
empty. Their generated constants (constructors, `rec`, `casesOn`, projections)
have none. A type whose statement hash differs after the run is a warning, not
a finding (decision D11).

The baseline is taken at the old toolchain before any edit. The after
certificate is taken at the new toolchain when the frontier is empty.
`compare` matches declarations by name, after the alias map.

The shell hashes the statement and body text with `String.hash` after
`AliasMap.normalizeWith`: the derived alias map, then the namespace moves of
the loaded `renamePrefix` rules (decision D5), at both toolchains. So a pure alias rename changes
neither hash, and it needs no card.

`statementHash` is the invariant's statement check. lean-mend does not edit a
statement region, so a difference can come only from an alias rename, and the
alias map removes that difference. The elaborated `type` can change across
toolchains for reasons outside the target (a renamed instance, a changed
notation). lean-mend reports a `type` difference but does not refuse on it.
See [decisions.md](decisions.md), Q1.

#### Why the statement is a token sequence

EquiVM run 7 halted with `invariantBroken` at `Reasoning.WordArithmetic`. The
statement of `Reasoning.Theory.u256_lor_ne_zero_right` had a line break after
the colon at v4.29.0 and none at HEAD. The probe then hashed the raw text of
the statement region, so a layout edit counted as a statement change.

The certificate compares the token sequence. The alternatives are worse:

- Text with whitespace collapsed to one space still differs on `x :T`
  against `x : T`.
- The elaborated type differs across toolchains for reasons outside the
  target, as the paragraph above states.

The remaining risk: two statements with the same tokens but a different
layout-sensitive parse compare equal. Lean parses some syntax by column (for
example a `by` block or a `do` block inside a statement), so the same tokens
in a different layout can parse to a different term. lean-mend edits a
statement only under `--annotate-binders` or `--follow-definition-changes`,
so such a difference can come from the bump commit itself. The certificate
does not see it.

`tests/statement-change.sh` checks both sides: a statement that differs only
in a line break and one space ends `done`
(`tests/fixtures/statement-layout`), and a statement that differs in one
token halts with `invariantBroken` (`tests/fixtures/statement-token`).

#### Every selected declaration has a row

The certificate selects a constant when its name is not internal, it has a
declaration range, and the node of its file at the start of that range
declares it. The node is a declaration, or a command with a statement
region, such as a theorem that a command macro makes (Mathlib's `lemma`).
The node declares the constant when its `declId` is a suffix of the name,
with `_root_.x` read as `x`, or when it has no `declId`. An `axiom`, and an
`opaque` with no value, has its signature as its statement and an empty
body. A constant whose range starts inside a command but not at such a node
is generated by that command (a constructor, a projection, a `where`
function, the parser of a `notation`), and it has no row. An instance that
`deriving` makes, and its auxiliaries such as `instInhabitedPools.default`,
start at the class name in the `deriving` clause, inside the type command,
so they have no row (`tests/cert-generated.sh`).

For each selected constant, the probe gives a row or an `unread` line. The
shell stops the run on an `unread` line with the typed error `DeclUnread`
(exit 3, ledger line `declUnread`), which names the module and the
declaration (`tests/cert-unread.sh`). No row is left out in silence.

Before this rule, the probe parsed each declaration alone, at its range,
with the environment of the batch and no `open` or `namespace`, and it left
out a row that did not parse. The run 7 baseline had no row for
`UniswapV2Pair.evalExpr_constructor_thisWord`, whose statement holds
`addressAsUint256 this`.

How the probe parses a file (`fileCommands` in `probe/Probe.lean`): it reads
the file's commands in order, as Lean does, with the scopes after the command
before. It elaborates only two kinds of command: the scope commands
(`namespace`, `section`, `end`, `open`, `set_option`), and a `local` command
that declares syntax (`notation`, `syntax`, `macro`, `elab`, mixfix,
`binder_predicate`). The environment already holds the module, so its other
syntax is known. The probe elaborates no declaration and no proof. A command
that has a parse error makes each declaration in it `unread`. A module that
builds has no parse error, so a parse error shows a difference between the
probe's parse and Lean's.

The environment of a `decls-batch` holds every module of the batch. On
EquiVM at v4.33.1, `Examples.UniswapV2Pair.SpecSyntax` imports
`Stele.Notation`, which declares the token `this`
(`syntax:max "this" : solExpr`). In a batch with `SpecSyntax`, four
declarations of `Examples.UniswapV2Pair.Spec`, `def this : Expr := …` among
them, do not parse. `Spec` does not import `Stele.Notation`, and in its own
environment all 151 commands parse. The statement of
`evalExpr_constructor_thisWord` behaves the same: in the environment of
`ConstructorDomainHashRuntime` its file parses, and with `SpecSyntax` added
two commands do not parse. So the shell reads a module with an `unread` line
again alone (`Target.declsOf`), and a batch of one module has the module's
own environment. An `unread` line of that run stops the run
(`tests/fixtures/statement-batch-token`).

Known limits, each a parse error and so a stop, never a lost row: syntax
that a file declares without `local` is known from the start of the file,
not from its declaration; a command of another kind that declares local
syntax (a macro of the file that expands to `local notation`) is not
elaborated (`tests/fixtures/cert-unread`).

Cost, measured on the 33 built modules of `Examples.UniswapV2Pair` at
v4.33.1, in one `decls-batch` process, on a shared host (load average 23 to
63 on 32 cores):

| Way to get the commands | Wall time | Peak resident size |
|---|---|---|
| before: parse at each range, batch environment, no scope | 477.9 s, 259.8 s again | 3.5 GB, 4.2 GB |
| `fileCommands` in the batch environment | 59.0 s | 4.2 GB |
| elaboration of each file (`Language.Lean.process`, as `regions`) | 27.2 s to 423.9 s per file, mean 106 s on 11 files | |
| an import of each module alone in the batch process | killed after 59 rows, 1992.7 s | 98 GB |

An EquiVM run builds about 890 modules (run 8: 892 in the build, 22 569
baseline rows). At 106 s per file, the elaboration of each file costs about
26 CPU hours per certificate, and a run takes two certificates. So the probe
parses and does not elaborate. Lean does not free an import, so a second
import in the batch process is not possible; the read of a module alone is
a probe process of its own. The `fileCommands` row was measured before the
last two changes to the probe (the `local` rule and the command nodes after
`in`), which do not change the work per command.

### The structural checks

They read the syntax tree from the probe, not the text:

- The edit range is inside one declaration's body region, or the edit is a
  derived alias rename.
- The candidate adds none of: `sorry`, `admit`, `axiom`, `native_decide`,
  `implemented_by`, `extern`, `unsafe`, `opaque`.
- The candidate removes no declaration and adds no declaration.

### Conformance for definition changes

A changed definition can change what the target computes. A rebuild cannot
show this. The check is differential: the same inputs go to the old
definition at the old toolchain and to the new definition at the new
toolchain, and the outputs must be equal.

- Inputs come from the target's own conformance suite, if it has one (EquiVM
  has the Ethereum test vectors). Otherwise they come from Plausible
  generators, if the input types have `SampleableExt` instances.
- The probe evaluates the definition at each toolchain and prints the outputs
  with `Repr`.
- The result is evidence on a **Behavior** card. A person accepts or rejects
  the change. A definition with no inputs available gets the card with the
  status `undecided` and the reason.

### Cards

A card shows only generated data (concept C10). Its fields:

| Field | Content |
|---|---|
| Rule | the rule or agent that made the change, in prose, with its provenance |
| Trace | the ledger entries for the site: diagnostic, candidates tried, verdicts |
| Status | `held`, `violated` or `undecided`, computed |
| Evidence | the diff, the certificate rows before and after, the conformance outputs |
| Counterexample | the first input where old and new outputs differ, if any |

Card kinds in lean-mend:

| Kind | Issued when |
|---|---|
| Behavior | a definition change was accepted |
| Violation | an axiom set differs from the baseline |
| Spec | a proposed rule waits for ratification |
| Decision | a choice the machine cannot make, for example a target that pins two toolchains |
| Held | the run report: every invariant part held, for the record |

A judgment records the person, the time and the answer in the ledger. A
rejected Behavior card reverts the patch and marks its site residue (not built
yet: today the judgment is recorded and the finding stays open).

At `certificate` the shell saves `.lean-mend/session.json` (the context, both
certificates, the residue, the cards) and writes `.lean-mend/cards/<id>.md`.
`lean-mend judge` loads the session, replays the ledger's judgments through
`RunState.close`, and steps the machine with the new judgment. Counterexample
is not computed yet; the card says so.

### What a card explains

A card states the cause of its finding, not only its effect. The judge must not
need to find the cause by hand.

- A Violation card holds, for each axiom added or removed, the shortest
  dependency path from the declaration to that axiom at each toolchain. It
  marks the first constant on the path whose own axiom set differs between the
  two toolchains, with that constant's module and package revision. That
  constant is the cause.
- A Behavior card holds the body diff in source text, the lean-mend commits
  that changed the body with their rules, and whether the change is inside a
  proof term only. A proof term does not change what the definition computes.
- Cards that share one cause name it once and list each declaration.

EquiVM run 10 (2026-11-07) is the measured case. 38 of its 43 Violation cards
added `Classical.choice` through one constant, Mathlib's `List.find?_congr`,
which v4.33.1's Mathlib proves with `grind`. Its 2 Behavior cards changed only
the tactics of a length proof inside the body.

## 2. lean-mend is correct

### Proofs in `Spec`

Proved now (`lake build` checks them; `#print axioms` shows only `propext`,
`Quot.sound` and `Classical.choice`):

- **Branch soundness.** `branchSound`: every patch on the mend branch has
  its error count fall and is clean, because `Accepted` carries the evidence.
- **Compare soundness.** `compare_nil`: no finding means `NoHarm`.
- **Indexed compare.** `compareIx_eq`: `compareIx` over a `CompareIndex`
  gives the same findings as `compare`, in the same order. `RunState.close`
  runs `compareIx`. `compare` looks up each baseline declaration in the
  lists of the after certificate and the alias map. On EquiVM run 10 (22576
  declarations, 3382 alias pairs), one `lean-mend judge` took 38 to 44 min.
  `compareIx` looks up each name in a hash map, and the same call takes 0.5 s.
- **Termination.** `Mending.step_measure`, `openCount_finish`,
  `openCount_settled`, `frontier_open` (see [machine.md](machine.md)).

To prove next:

- **Frontier completeness.** A module that fails with every import built is
  in the frontier.
- **Alias resolution.** `AliasMap.resolve` returns a map with no chain, or
  `none` only on a cycle.

A gate rejects `sorry` in `Spec` and `Core`.

### Properties on `Core`

Plausible properties over generated inputs, for what is not a theorem yet:
`classify` is total on recorded diagnostics; the alias resolver ends on
acyclic maps and refuses cyclic ones; candidate order respects entrenchment.
A property counts only if it runs (concept D9).

### Fixtures

`tests/fixtures/` holds one small Lake project per error class. Each pins an
old and a new toolchain, breaks in exactly one known way, and has an expected
after state. `lake test` runs lean-mend on each fixture and checks the ledger,
the branch and the certificate. The fixtures together form the tour: every
transition of the machine fires at least once (concept D7).

### The acceptance test

The EquiVM test in [what-lean-mend-is.md](what-lean-mend-is.md). It runs
against the real repository, the real toolchains and the real Lake. There is
no mock in its path.
