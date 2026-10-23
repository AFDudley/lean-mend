# Glossary

One word means one concept. Code, docs and the ledger use these words and no
synonyms. A new term enters here before it enters code (stratum 0, see
[process.md](process.md)).

## The target and its versions

**target** (n) — The Lake project that lean-mend mends. It is not lean-mend
itself (see "source" below).

**source** (n) — lean-mend's own repository: its rules, its machine and its
probe. The source judges; the target is judged.

**toolchain** (n) — A Lean release, named as in `lean-toolchain`, for example
`leanprover/lean4:v4.33.1`.

**bump** (n) — The change of a target from an old toolchain and old dependency
revisions to new ones. A bump is an input to lean-mend. lean-mend does not
choose it.

**module** (n) — One Lean source file and the `.olean` it builds. Modules form
a directed acyclic graph by `import`.

**frontier** (n) — The failing modules whose imports all build. Only a frontier
module can be repaired; every other failing module waits.

## Failures

**diagnostic** (n) — One message from the Lean compiler, read from
`lean --json`: a position, a severity and a text. A diagnostic is raw input.

**site** (n) — A position in a target module where a diagnostic of severity
error starts, with the smallest syntax node that contains it.

**error class** (n) — The kind of a site's failure, computed from its
diagnostic and its syntax node. An error class is derived, never stored on the
site.

**timeout class** (n) — An error class for a resource limit. lean-mend knows
two: `heartbeat` (deterministic, a limit inside Lean) and `wallclock`
(contention on the host).

## Repairs

**rule** (n) — Data that maps an error class and a syntax pattern to an
ordered list of candidates. Every rule has an entrenchment and a provenance.

**candidate** (n) — One edit that a rule proposes for one site.

**patch** (n) — A candidate applied at a site, with the module rebuilt.

**accepted patch** (n) — A patch whose module builds and whose module passes
the invariant check.

**residue** (n) — A site for which every candidate of every matching rule
failed, or for which no rule matched.

**proposed rule** (n) — A rule that an agent or a person wrote from a residue
repair. It is not ratified.

**ratified rule** (n) — A rule that passed the fixed runner on the required
number of independent sites. Only ratified rules run without a card.

**entrenchment** (n) — The firmness of a rule: `derived` (computed from the
new libraries, such as a deprecated alias), `ratified`, or `proposed`. A firmer
rule runs first.

## Proof of no harm

**certificate** (n) — A record of a target at one toolchain: the modules that
build, and for each declaration its kind, its statement text, its statement
hash and its axioms.

**baseline certificate** (n) — The certificate at the old toolchain, taken
before lean-mend edits anything.

**after certificate** (n) — The certificate at the new toolchain, taken when
lean-mend stops.

**statement region** (n) — The syntax region of a declaration's name, binders
and type. lean-mend does not edit it, except for an alias rename.

**body region** (n) — The syntax region of a declaration's value: a proof term,
a tactic block or a definition body.

**definition change** (n) — An accepted patch inside the body region of a
`def`, `instance` or `abbrev`. A definition change can change what the target
computes. It needs a semantic check and a card.

## The program

**probe** (n) — A small Lean program that runs under the target's toolchain
and writes JSON. It reads what only the target's own Lean can read: syntax
spans, statement hashes, axioms and deprecated aliases.

**machine** (n) — lean-mend's state machine: its states, transitions and
refusals. See [machine.md](machine.md).

**refusal** (n) — A value that a transition returns when it cannot advance. It
names the reason. It is never an exception.

**ledger** (n) — The append-only record of every attempt, verdict and
judgment, in `.lean-mend/ledger.jsonl` in the target.

**judgment** (n) — A decision that a person or an agent made and that the
machine trusts, recorded with who made it, when, and under which doctrine.

**card** (n) — The form in which a person makes a judgment: the rule in prose,
the formal statement, the trace, the generated status and the evidence. A card
shows only generated data.

**fixed runner** (n) — The part of lean-mend that grades a proposal. It comes
from the source, never from the target or from the proposer.
