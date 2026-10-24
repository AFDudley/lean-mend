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
- `statement`: the source text of the statement region, with whitespace
  normalized;
- `statementHash`: `String.hash` of `statement` after `AliasMap.normalize`;
- `type`: the elaborated type, printed with `pp.all`, for the report only;
- `axioms`: the axioms the declaration depends on, by the method of
  `#print axioms`.
  The shell keeps them as a sorted set, and it collapses every generated
  `native_decide` axiom (`X._native.native_decide.ax_1_12`) to the one name
  `native_decide`. Lean numbers those per declaration, so their names can
  change between toolchains when the trust does not. EquiVM's certificates
  rest on them.

The certificate holds only declarations that the source declares: the probe
keeps a constant only if the command at its source range declares that name,
or declares no name (an anonymous `instance`). Compiler-generated constants,
for example the instances that `deriving BEq, Inhabited, Repr` makes, are
excluded. Their source range is inside another command, so the first probe
recorded another declaration's statement for them, and Lean versions differ in
which ones they generate. On EVMLean, `Ethereum.instInhabitedBlockHeader.default`
exists at v4.29.0 and not at v4.33.1, and that halted the run with
`invariantBroken` before this filter.

Not covered yet: inductive types, structures and classes have no `declSig`
or `declVal`, so the probe records no row for them, and the invariant does not
check their constructors. EVMLean's `account_change_consistent` needed a
constructor-binder change at v4.33.1 (`{σ σ'}` → `{σ σ' : AccountMap}`); that
is a statement edit, so it stays residue for a person.

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

## 2. lean-mend is correct

### Proofs in `Spec`

Proved now (`lake build` checks them; `#print axioms` shows only `propext`,
`Quot.sound` and `Classical.choice`):

- **Branch soundness.** `branchSound`: every patch on the mend branch has
  its error count fall and is clean, because `Accepted` carries the evidence.
- **Compare soundness.** `compare_nil`: no finding means `NoHarm`.
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
