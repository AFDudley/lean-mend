# Decisions

## D1. lean-mend is written in Lean, end to end

**Decision.** Spec, core and shell are Lean 4 in one Lake package.

**Reasons.**
- The operator decided "use Lean to build the machine".
- The Lean-first rulings (sessions `01a162aa` and `01a16286`, 2026-10-22) make
  Lean the specification substrate. A gap becomes a definition that cannot be
  written.
- The domain is Lean. Its parser, its JSON and its process API are in core
  Lean.
- With one language, the boundary between spec and implementation is one
  theorem per core function, not a translation.

**Rejected.** Bend2 for the core with a Python shell, as in exophial4
(`docs/labbook/bend2-for-the-core-and-lean-for-the-specs.md`). For lean-mend
that adds a second language and a second toolchain pin, and Lean already
reaches the shell.

## D2. lean-mend pins Lean v4.35.0

The newest stable release on 2026-10-23. lean-mend itself has no Mathlib
dependency, so a bump of lean-mend is cheap, and lean-mend mends itself.

## D3. A probe crosses the version boundary

The machine never imports a target module. A small probe runs under the
target's toolchain and writes JSON (see [architecture.md](architecture.md)).
The `.olean` format and the internal API differ between releases, so no other
design reads statements, axioms or syntax from a target at another version.

## D4. Lake owns the target build

lean-mend calls `lake build`, and `lake env lean --json` only for diagnostics
of a failing module. It does not write `.olean` files itself. Lake's traces
stay valid, and a person can run `lake build` on the mend branch with the same
result.

## D5. No statement edit, except an alias rename

The edit type cannot address a statement region. Two exceptions rename a
constant, and the statement hash is computed after the rename on both sides:

- a deprecated name to its alias target, which the probe reads from
  `@[deprecated]`: by construction;
- a namespace move declared by a `renamePrefix` rule (Batteries v4.33.1 moved
  `Batteries.RBMap` to `RBTree.RBMap` with no aliases): by judgment. The rule's
  claim, "the same constants under a new name", is ratified by a person on the
  rule's Spec card. The certificate cannot check it.

Without the second exception, the EVMLean run halted with `invariantBroken`
at `Conform.Wheels`, whose statements name `Batteries.RBMap`.

## D6. The scheduled form is a CI workflow in the target

The workflow runs `lean-update` or `lean-bump`, then `lean-mend run --adopt`
on a red build, and opens one pull request with the open cards. lean-mend does
not move pins (out of scope). A person answers the cards on the pull request.

## D7. The Goedel workbook scripts are not reused

`mike1729/goedel-workbook-lean427` is regex over text in Python, with one
commit and no tests. lean-mend takes its method (compile, classify, repair by
class, compile again; `first | … | skip` chains) and none of its code.

## D8. The name

`lean-mend`. `lean-bump` (paulbutcher/lean-bump) and `lean-up` (Lean-zh) are
taken. `leanmigrate` is an unrelated SQL tool.

## D9. Human judgments are cards

Definition changes, axiom differences and rule ratification go to cards (see
[verification.md](verification.md)). No count of automated successes replaces
a card.

## D10. lean-mend is a dumb port: it never adds a declaration

lean-mend changes the bodies of declarations that already exist, and the
renames of decisions D5. It never adds a `def`, `theorem`, `lemma`,
`instance`, `inductive` or any other declaration, and no candidate, rule or
agent repair may do so (structural check 3 in `machine.md`). The operator
decided this on 2026-10-24.

The reason: a new declaration adds a statement that the baseline certificate
has no row for, and a new `@[simp]` lemma changes what `simp` does in every
later proof. That is new code, not a port.

Example: for EVMLean v4.33.1 the hand bump added three `@[simp]` projection
lemmas for `State.subtractGas` in `Theory/GasLemmas.lean`. lean-mend instead
adds `Ethereum.State.subtractGas` to the existing `simp` sets
(`rules/proposed/evmlean-subtractGas-unfold.json`); on the real file this
removed 8 of 33 errors.

## D11. Types are in the certificate; lean-mend narrows them only on request

The operator decided this on 2026-10-24.

- The certificate records every `inductive`, `structure` and `class`. A type's
  statement is its whole command: its fields or constructors define it.
- lean-mend does not edit a type. If a type's text differs after the run, the
  run reports a warning (`typeChanges`). A warning does not block `done` and
  needs no card.
- One edit to a type exists: narrowing. At Lean v4.33, a constructor binder
  without a type that repeats a section `variable` (`{σ σ'}`) is an error
  (`binderOverride`). Lean's own hint is to give it a type. lean-mend proposes
  `{σ σ' : _}` for every names-only binder group of that type, in one edit,
  because Lean reports only the first group.
- By default lean-mend applies nothing: it writes a warning with the exact
  edit, and the site is residue. With `--annotate-binders` it applies the
  edit, and the type change then appears as a warning.

EVMLean `Theory/AccountLocality.lean` (`account_change_consistent`): on the
real file the narrowing took the errors from 86 to 14.

## D12. A statement may follow a definition change, only on request

The operator decided this on 2026-10-24.

A theorem's statement can restate a definition's code. When lean-mend changes
that code in the definition's body (EVMLean: `match p with` over precompile
numbers became `match p.val with` in `Semantics`), the statement no longer
compiles, and it must change the same way to stay about the same thing.

- With `--follow-definition-changes`, the `match` operations of a rule that
  was already accepted in a declaration body this run may also edit a
  statement (`EditTarget.followStatement`). Each such change is a warning,
  and the after certificate lists the declaration in `followed`, which part 1
  of the invariant allows.
- Without the flag, the run writes a warning with the edit, and the site is
  residue.

EVMLean `Theory/AccountLocality.lean` 2359, 2379, 2393: the hand bump made the
same change.

## D13. Axiom findings extend `ErrorClass`, with one more rule field

**Decision.** `ErrorClass` gains `axiomsAdded` and `axiomsRemoved`
(`docs/verification.md` § The cause, `Change`). A rule for either class
gains `causeTag`, matched against the cause constant's shape
(`docs/rules.md` § Axiom-finding rules).

**Reasons.**
- One rule file format, one loader, one vacuity check (concept C9), for
  every rule, diagnostic-triggered or finding-triggered (concept B9).
- `classify` stays total over `Diagnostic` (concept B4); a separate pure
  function, `classifyCause`, is total over `AxiomCause`. Neither function
  grows a case the other must also handle.

**Rejected.** A parallel `FindingClass`/`FindingRule` type. It would need
its own loader, its own vacuity check, and its own ordering rules
(`docs/rules.md` § Entrenchment and order) — three duplicated mechanisms for
one new trigger.

## D14. The site of an axiom finding is the nearest owned constant, not the finding's own declaration

**Decision.** Walking the cause's `path` from the axiom toward the
declaration, the site is the first **owned** constant, after a generated
auxiliary gives its place to the declaration that owns it: the same rule
`pickCause` already applies to the cause (`docs/machine.md` § The site of
an axiom finding).

**Reasons.**
- EquiVM run 10's 38 G1 cards share one site this way,
  `Reasoning.Theory.selectorDispatchMsg_eq_dispatchList`, matching the one
  edit the hand repair made (`.scratch/axiom-fix/edits.md` § Edit E1). The
  finding's own declaration, taken literally, would give 32 different sites
  for the same cause, 31 of them in modules that do not define the lemma
  that needs the edit.
- One repair then closes every finding whose path reaches that site, so the
  Level 3 measure (`docs/machine.md` § Termination, Level 3) falls once per
  repair, not once per card.
- EquiVM run 10's single G3 card needs the owner rule
  (`.scratch/axiom-fix/edits.md` § Edit E3). Lean compiles
  `allocationSizes`'s own `match` into a generated matcher,
  `allocationSizes.match_1`, the cause. The path to it runs through a
  well-founded-recursion helper, `allocationSizes._f`, also generated.
  Neither has a source declaration of its own to edit. The owner rule gives
  both their place to `allocationSizes`, the declaration Edit E3 changed.
  Without it, the site would be `allocationSizes._f`, which no rule can
  repair.

## D15. Level 3's acceptance check rebuilds the site's module only; importers are rebuilt only when the edit can change computation

**Decision.** An attempt's acceptance check (`docs/machine.md` § Acceptance)
rebuilds the site's module. For a proof-only edit, the importers' axiom sets
come from a walk over the current build's constant graph, with the site
module's new axiom sets substituted. Importers are rebuilt only when the edit
can change what a declaration computes, and then only the importers that use
a changed declaration.

**Reasons.**
- A proof-only edit keeps the declaration's statement, and every importer uses
  the declaration only through its statement (proof irrelevance). So no
  importer's term changes and no importer can get a new build error; a rebuild
  of the importers measures nothing that the walk does not.
- The walk reads each importer's own edges from the current build, so an axiom
  that an importer picks up by its own tactics still shows.
- Cost: a rebuild of every importer runs once per candidate, not once per
  finding. For EquiVM's G1 group that is 84 importers and about 16 minutes
  serial for each candidate; the walk costs one module's elaboration.
- Measured: `.scratch/axiom-fix/edits.md` § Edit E1 gave the baseline axiom
  set for all 31 cross-module cards by the walk, and the control walk without
  the substitution reproduced `Classical.choice` for all 31.

**Rejected.** A rebuild of every importer for every candidate. An earlier draft
of this decision chose it, on two claims: that only a rebuild shows a new
build error in an importer, and that the walk misses an axiom an importer picks
up by itself. Neither holds for a proof-only edit, by the reasons above.

## D16. A theorem's repaired proof needs no card; a computing declaration's proof-only repair auto-accepts one

**Decision.** A repair inside a `theorem`'s body needs no Behavior card
(`kind.computes = false` already excuses it, `docs/machine.md` § The
invariant). A repair inside a `def`, `instance` or `abbrev` whose changed
bytes lie wholly inside a proof sub-term of the body auto-accepts a Behavior
card, evidenced by the same proof-only test a person's card already uses
(`docs/verification.md` § The body change); a repair that touches the data
component still needs a person's card.

**Reasons.**
- Proof irrelevance: two proofs of the same proposition compute the same
  thing. The test is already machine-decidable (it is how EquiVM's own c-1
  and c-2 Behavior cards were judged, `docs/verification.md` § The empty
  Trace of run 10), so running it again for every repair is not a new kind
  of trust, only an automated instance of a check a person already does by
  eye.

## D17. `beforeDecl` needs the enclosing `mutual`'s start, not the declaration's own

**Decision.** `DeclRegion` gains `mutualStart : Option Nat`: the byte offset
of the smallest enclosing `mutual`, when the named declaration is a member
of one. `locate` reports it in place of `declStart` when it is `some`.

**Reasons.**
- `set_option … in` before one member of a `mutual` block scopes the option
  to that member's own elaboration; the matcher Lean compiles for the whole
  mutual group reads the option active when the elaborator reaches the
  `mutual` keyword, before any member (`.scratch/axiom-fix/edits.md` § Edit
  E3). `match-sparse-cases` (`docs/rules.md`) needs the fix to repair a
  mutual-nested matcher; `heartbeats`/`setOptionBefore` (decision B1,
  `docs/breaking-changes.md`) needs it for the same reason on any
  mutual-nested declaration, not only for an axiom finding.

# Open questions

**Q1. Which statement identity across toolchains?** The source statement hash
is stable when lean-mend does not edit statements, but it does not detect a
statement whose meaning changed because a notation or a coercion changed
upstream. The elaborated type detects that, and also differs for harmless
reasons. Choice to make: report only (the current design), or a card for
every elaborated-type difference.

**Q2. Deprecation warnings.** A deprecated name is a warning at the bump where
it is deprecated, and an error when it is deleted, often several releases
later. lean-mend could rename deprecated uses before they break. The current
design repairs errors only.

**Q3. How residue reaches an agent.** Options: a residue packet as an exophial
intake in the lean-mend repository, or a direct agent call from the CLI. The
fixed runner is the same in both.

**Q4. Bisect cost on Mathlib.** Each step needs the Mathlib cache for that
commit. Old commits can lose their cache. A step without a cache is "unknown"
in the bisection, so attribution can stop at a range, not a commit.
