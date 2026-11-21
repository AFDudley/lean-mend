# The concepts lean-mend embodies

Functional core, imperative shell is one concept of many. This document lists
every concept the design takes from exophial, exophial3 and exophial4, and the
concepts that lean-mend adds. Each entry gives a definition, what it means for
lean-mend, and its source.

Source paths are relative to `~/code/git_puller/repos/`. `x1` is `exophial`,
`x3` is `exophial3`, and `x4` is `exophial4`. A research pass on 2026-10-23
collected these concepts; the paths were checked to exist on that date.

## A. The shape of the program

**A1. Functional core, imperative shell.** Pure decisions sit in a core with
no IO. A thin shell does all IO. *lean-mend:* classification, frontier
selection, candidate ordering and the verdict on an attempt are pure Lean
functions in `LeanMend/Core`. Running Lake, reading JSON, editing files and
git sit in `LeanMend/Shell`. *Sources:* `x4/docs/layout.md`; `x3/src/e_new_model/docs/2026-09-01-the-driver-is-the-imperative-shell-composition-root.md`.

**A2. The positional boundary.** The boundary is a directory, so a gate can
check it: nothing under the core imports IO. *lean-mend:* no module under
`LeanMend/Core` or `LeanMend/Spec` imports `IO`-producing APIs; a gate checks
the import graph. *Source:* `x4/docs/process.md` (the core-or-shell rule).

**A3. The composition root is the driver.** One place in the shell wires the
adapters to the pure transitions. *lean-mend:* `LeanMend/Shell/Driver.lean` is
the only module that knows both the machine and the adapters. *Source:*
`x3/.../2026-09-01-the-driver-is-the-imperative-shell-composition-root.md`.

**A4. The version boundary (new).** lean-mend runs on its own toolchain. The
target runs on another. What only the target's Lean can read (syntax, statement
hashes, axioms, deprecated aliases) is read by the probe, which runs under the
target's toolchain and writes JSON. The machine never links the target's Lean.
*Source:* this design; the EquiVM experience, where `DumpAxioms.lean` had to
run inside the target to read its axioms.

**A5. Stratified design.** A system is a sequence of levels. The parts of one
level are the primitives of the next. *lean-mend:* glossary → types →
invariant → parsed inputs → flat chart → total transitions → shallow run →
properties. *Sources:* `x4/docs/process.md`; `x4/docs/the-bottom-up-language.md`.

**A6. Literate code.** Directory structure, imports and comments are enough to
modify a file. Comments cite the design document by path. *lean-mend:* each
module's docstring cites the section of this design that it implements.
*Source:* `x1/docs/METHODOLOGY.md`.

## B. Types and states

**B1. Illegal states are unrepresentable.** One type per legal state. No
optional fields that allow combinations that never occur. *lean-mend:* an
`Accepted` patch carries the rebuild evidence as a field; a value without the
evidence cannot be built. *Sources:* `x4/docs/process.md` (stratum 1);
`x4/doctrine/worker.md`.

**B2. Parse, don't validate.** Raw input becomes a precise type at the edge.
Nothing downstream checks it again. *lean-mend:* `lean --json` lines and probe
JSON become `Diagnostic`, `Site` and `Certificate` values once, in the shell.
The core receives only typed values. *Source:* `x4/docs/process.md`
(stratum 3); `x4/docs/the-types.md`.

**B3. State the invariant before any transition.** The one invariant the
machine must never violate is written first, as a predicate. *lean-mend:* the
invariant is a Lean `Prop` in `LeanMend/Spec/Invariant.lean`, stated before the
step function exists (see [machine.md](machine.md)). *Source:* `x4/docs/process.md`
(stratum 2); `x4/docs/the-core-object-model.md`.

**B4. Totality by the type checker.** Every branch over a closed set is
exhaustive, and the checker proves it. *lean-mend:* Lean's `match` is total by
construction. A new error class added to the inductive type breaks every
function that does not handle it. *Source:* `x4/docs/process.md` (stratum 5).

**B5. A refusal is a value.** A transition that cannot advance returns a
refusal with its reason. No exception crosses the core. *lean-mend:* `step`
returns `Except Refusal State`, and `Refusal` is a closed inductive type.
*Source:* `x4/docs/the-types.md`.

**B6. A state is not its history.** A state holds no predecessor field. History
is read from the log. *lean-mend:* the state of a site holds the candidates
still to try, not the ones already tried; the ledger holds the attempts.
*Source:* `x3/src/e_new_model/docs/2026-08-16-a-state-is-not-its-history.md`.

**B7. Draw the chart flat first.** Nest a state only when siblings share a
transition or an action. *lean-mend:* `Mending` is the one composite state, and
only because every site in it shares the revert and the invariant check.
*Source:* `x4/docs/process.md` (stratum 4).

**B8. Refine one level at a time.** Write the gluing invariant between levels
before the new transitions. Finish a level when nothing is left to prove.
*lean-mend:* level 1 is the module-level machine; level 2 adds sites and
candidates inside `Mending`. *Source:* `x3/src/e_new_model/docs/2026-08-30-refine-one-level-at-a-time.md`.

**B9. Representation minimality.** Keep the coarsest representation that still
states the invariant. Two error classes with the same rules are one class.
*Source:* `x3/src/e_new_model/docs/2026-08-30-representation-minimality-is-decomposition.md`.

## C. Knowledge, judgment and trust

**C1. An oracle is a decision procedure.** Acceptance checks, preservation
checks and gates are one substrate, a decision over an artifact. *lean-mend:*
"the module builds", "no statement changed" and "the axiom set is the same"
are oracles with typed verdicts. *Source:* `x4/docs/the-core-object-model.md`.

**C2. Verification is structural or observational.** A check either reads
shape (parse, AST) or observes a run. Semantic judgment is a residue to shrink.
*lean-mend:* "the patch did not touch a statement region" is structural;
"the module builds" is observational; "the definition still computes the same
thing" is the residue, sent to a card and a conformance suite. *Sources:*
`x4/docs/labbook/verification-is-ast-decidable-or-observational-not-semantic.md`;
`x4/docs/test-validity.md`.

**C3. Entrenchment.** Oracles and rules rank by firmness. A mined or proposed
rule never overrides a derived or ratified one. *lean-mend:* rule order is
`derived` > `ratified` > `proposed`. *Source:*
`x3/docs/labbook/every-oracle-is-a-ratified-oracle-at-some-entrenchment.md`.

**C4. A proposal is graded by a fixed runner.** An agent drafts. A runner that
the agent does not control grades the draft. Only the runner promotes it.
*lean-mend:* an agent's residue repair becomes a proposed rule. The fixed
runner replays it on other sites before it is ratified. *Sources:*
`x3/.../2026-09-08-extraction-of-a-statechart-is-a-judgment-and-a-fixed-runner-grades-its-draft.md`;
`x3/.../2026-09-01-a-behavioral-oracle-emits-and-a-fixed-runner-judges.md`.

**C5. Decomposition is a checked proposal.** A split of a claim is accepted
only after cheap decidable checks, in order of cost. *lean-mend:* a module's
failures split into sites; a site is repairable only when its upstream modules
build (the frontier check), which is the cheap check. *Source:*
`x3/src/e_new_model/docs/2026-08-15-decomposition-is-a-checked-proposal.md`.

**C6. Judgment attribution.** Every decision the machine trusts records who
made it, when, and under which doctrine. It is never re-checked silently.
*lean-mend:* card answers and agent repairs are `Judgment` records in the
ledger. *Source:* `x4/docs/the-core-object-model.md`; `x4/docs/the-types.md`.

**C7. The trust partition.** What decides (rules, the runner, the probe, the
gate configuration) comes from where the worker cannot write. Only the product
comes from the worker. *lean-mend:* rules and the probe come from the
lean-mend install, never from the target tree or from an agent's output. An
agent's edit is the product; it never grades itself. *Source:*
`x1/docs/VERIFICATION.md` (the trust partition; the exo-815 lesson, where a
worker rewrote its own spec and the grader ran the rewrite).

**C8. Deterministic grading.** Every verdict is reproducible without an LLM.
An LLM may draft; it never grades. *Source:* the Lean-first rulings, sessions
`01a162aa` and `01a16286` (2026-10-22); `x4/docs/labbook/bend2-for-the-core-and-lean-for-the-specs.md`.

**C9. Vacuity.** A check that cannot fail checks nothing. *lean-mend:* a rule
whose pattern matches every site, or a candidate that is `skip` alone, is
refused by the rule loader. *Source:* `x1/docs/VERIFICATION.md` (the vacuity
gate).

**C10. Human judgment happens on cards.** A person sees the rule in prose, the
formal statement, the trace, the status and the evidence, all generated. The
answer is written back with the person and the time. *lean-mend:* definition
changes and proposed-rule ratification are cards. *Source:*
`x4/docs/labbook/bend2-for-the-core-and-lean-for-the-specs.md` (decision 5).

**C11. The source is not the target.** lean-mend's rules and machine are the
source. The project being mended is the target. They stay distinct even when
lean-mend mends itself. *Source:* `x3/docs/labbook/the-source-repo-is-not-the-target-repo.md`.

## D. Storage, concurrency and process

**D1. The two-store rule.** Git holds artifacts. The ledger holds intent and
verdicts. Neither holds the other's kind. State is derived by joining them.
*lean-mend:* the mended code is on a git branch in the target; the attempts and
verdicts are in `.lean-mend/ledger.jsonl`. *Sources:*
`x4/docs/the-core-object-model.md`; `x1/docs/decisions/2026-07-23-app-as-pure-object-exophial-as-total-operator.md`.

**D2. Monotone log, serialized operand (CALM).** A grow-only log needs no
coordination. The operand needs one writer. *lean-mend:* attempts on different
frontier modules may run in parallel in separate worktrees and append to the
ledger. Only one writer applies accepted patches to the mend branch. *Source:*
`x1/docs/decisions/2026-07-23-app-as-pure-object-exophial-as-total-operator.md`.

**D3. Worktree isolation.** Each attempt runs in its own worktree, so a failed
candidate cannot leave a trace in the mend branch. *Source:* `x1/docs/DESIGN.md`.

**D4. A completion is a typed handoff.** A "done" without its evidence cannot
be built. *lean-mend:* an `Accepted` patch must carry the rebuild verdict and
the invariant verdict. *Source:* `x1/docs/DESIGN.md` (completion is a typed
handoff).

**D5. Convergence is a fixpoint, not a counter.** A loop stops when a
well-founded measure stops decreasing, never at a retry cap. *lean-mend:* the
termination measure is in [machine.md](machine.md), and its decrease is a
theorem. *Source:* `x1/docs/decisions/2026-06-28-feature-as-assertions-pipeline-fsm.md`.

**D6. Fail fast.** No blanket catch. An unexpected error stops the run with its
cause. *Source:* `x1/docs/METHODOLOGY.md`.

**D7. The tour.** The shortest walk that fires every transition once is the
order of work and the baseline test. *Source:* `x4/docs/process.md` (the tour).

**D8. Checked coverage.** Every transition runs for real and its effect is
asserted. *Source:* `x1/docs/decisions/2026-06-28-feature-as-assertions-pipeline-fsm.md`.

**D9. A property is a run, not a name.** Coverage is measured by running, never
read from a list. *Source:* `x3/src/e_new_model/docs/2026-08-30-a-property-is-a-run-not-a-name.md`.

**D10. Stage 0.** The first complete machine is written by hand, runs end to
end against substitutes, and only then grows. *Source:* `x4/docs/the-bootstrap.md`.

## E. Assurance

**E1. Graded assurance.** Verification strength rises with the consequence of a
mistake. *lean-mend:* a rename by a deprecated alias needs only a rebuild; a
proof edit needs the rebuild and the axiom check; a definition change needs a
card and a semantic check. *Source:* `x1/docs/VERIFICATION.md` (the assurance
levels).

**E2. By construction or by verification, labelled.** Each guarantee says which
it is, and a verification is never relabelled as construction. *lean-mend:*
"lean-mend never edits a statement region" is by construction (the edit type
cannot address that region); "the axioms are unchanged" is by verification.
*Sources:* `x1/docs/motifs-and-constructible-software.md`;
`x1/docs/METHODOLOGY.md`.

**E3. Lean as the specification and proof substrate.** A precise definition
exposes a gap as a definition that cannot be written. A failed theorem returns
a witness. *lean-mend:* the machine, its invariant and its termination are
Lean definitions and theorems, and the implementation is the same Lean code.
*Sources:* sessions `01a162aa` and `01a16286` (2026-10-22);
`x4/docs/labbook/bend2-for-the-core-and-lean-for-the-specs.md`.

## Concepts considered and not adopted

- **Bend2 for the pure core.** The exophial4 labbook (decision 1) chooses
  Bend2 for exophial4's core because exophial4's shell stays in Python. For
  lean-mend the domain is Lean itself, Lean has the IO, JSON and process APIs
  the shell needs, and one language removes the boundary between core and
  shell. See [decisions.md](decisions.md), D1.
- **The thirteen motifs as a classifier.** The motif taxonomy says which
  representation fits a program. It does not classify compiler errors. Not
  used.
- **ACE / DRS / TPTP / eprover.** The Lean-first rulings replace this layer with
  Lean. lean-mend's vocabulary lives in [glossary.md](glossary.md) and in Lean
  types, not in ACE.

## Tensions

- **Purity against parallel attempts.** Attempts in parallel worktrees are
  shell work. The core decides which attempts may run together (independent
  frontier modules). The shell only executes that decision.
- **Proposed rules against entrenchment.** An agent's successful repair is
  valuable and unratified at once. It runs only after ratified rules, and only
  a card or the fixed runner can ratify it.
- **Statement immutability against renames.** A deprecated name inside a
  statement must change. The design allows exactly one statement edit: replace
  a name with its alias target, when the probe proves the alias. The statement's
  elaborated term is then identical.
