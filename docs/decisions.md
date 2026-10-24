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
