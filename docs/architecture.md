# Architecture

## Language

lean-mend is written in Lean 4, at the toolchain in `lean-toolchain`
(v4.35.0). The specification, the core and the shell are one Lake package. See
[decisions.md](decisions.md), D1.

## Layout

Files marked `*` exist. The others are the plan, in the order of
[process.md](process.md).

```
lean-toolchain
lakefile.toml
LeanMend/
  Spec/          Types, Props and theorems. No IO.
  * Types.lean       operands; the edit type has no statement constructor (B1)
  * Invariant.lean   NoHarm and BranchSound; imports no transition (B3)
  * Termination.lean the measure theorems (D5)
  Core/          Pure functions. No IO.
  * Classify.lean    Diagnostic → ErrorClass
  * Mend.lean        level 2: Mending, next, step, measure
  * Run.lean         level 1: RunState, frontier, Settled, alias resolve, step
  * Compare.lean     baseline × after → findings; compare_nil
    Propose.lean     Site × rules × AliasMap → ordered candidates
  Shell/         IO. Parsing at the edge, Lake, git, files, the ledger.
    Parse.lean       JSON → typed operands, once (concept B2)
    Lake.lean        build, per-module diagnostics
    Probe.lean       runs the probe under the target toolchain
    Edit.lean        applies a candidate as a byte-range replacement
    Git.lean         the mend branch and attempt worktrees
    Ledger.lean      append and replay
    Cards.lean       writes cards, reads judgments
    Driver.lean      the composition root (concept A3)
  Main.lean      the `lean-mend` executable
probe/
  Probe.lean     runs under the TARGET toolchain; writes JSON
rules/
  *.json         ratified rules; proposed rules in rules/proposed/
tests/
* Tour.lean      the tour of the pure machine; `lake test` runs it
  fixtures/      small Lake projects, each with a known break
```

A gate checks the boundary (concept A2): no module under `Spec/` or `Core/`
imports a module under `Shell/`, and no function under `Spec/` or `Core/` has a
type that ends in `IO _` or `EIO _ _`.

## Spec and core

`Spec` states what the machine must do. `Core` does it. `Spec/Types.lean` and
`Spec/Invariant.lean` import no `Core` module. `Spec/Termination.lean` imports
`Core`, because its theorems are about the `Core` functions.

## The version boundary

lean-mend runs on v4.35.0. A target runs on its own toolchain, for example
v4.29.0 before the bump and v4.33.1 after. Lean's `.olean` format and its
internal API change between releases, so lean-mend cannot import a target's
modules (concept A4).

The probe solves this. `probe/Probe.lean` is one small file. The shell copies
it into the target's scratch directory and runs it with
`lake env lean --run Probe.lean <command>` inside the target. It then runs
under the target's toolchain and sees the target's built modules. It writes
JSON to stdout. Its commands:

| Command | Output |
|---|---|
| `imports <file>…` | each file's imports, from its parsed header |
| `decls <module> <file>` | for each declaration of the built module: name, kind, statement text and byte range, body text and byte range, axioms (by `collectAxioms`, the method of `#print axioms`) |
| `deprecated <module>…` | every `@[deprecated]` declaration in the environment of the modules, with its new name, from `Lean.Linter.deprecatedAttr` |
| `goal <file> <pos>` | not built yet: the goal state at a position, from the info tree, for a residue packet |

The probe names no position type. v4.35.0 removed `String.Range` and made
`String.Pos` depend on its string, so the probe reads positions only through
`Syntax.getPos?`, `Syntax.getTailPos?` and `.byteIdx`, and slices UTF-8 bytes.
A declaration with an empty signature (`abbrev T := Nat`) gets an empty
statement range at the start of its body.

`tests/probe-matrix.sh` compiles and runs the probe under v4.29.0, v4.33.1 and
v4.35.0 against `tests/fixtures/probe-basic`, and checks each command's
output. A toolchain that breaks the probe is a red gate.

## Building the target

Lake owns the target's build products and their traces. lean-mend does not
replace Lake.

1. `lake build` builds the dependency packages and the target. The shell reads
   which target modules failed from Lake's exit and its job list.
2. For each failing frontier module, the shell runs
   `lake env lean --json <file>` and parses the diagnostics. This is the second
   compile of a failing module only.
3. An attempt edits one file in an attempt worktree and runs
   `lake build <module>` there. Lake rebuilds only that module, because its
   imports are built.

Modules are handled in graph order (brief item 1). Independent frontier
modules may be attempted in parallel, each in its own worktree (concept D3).

## The two stores

| Store | Holds | Location |
|---|---|---|
| git | the target's code, and one commit per accepted patch | the branch `lean-mend/<old>-to-<new>` in the target |
| ledger | every observation, attempt, verdict, card and judgment | `.lean-mend/ledger.jsonl` in the target, committed on the mend branch |

Git never holds a verdict as a file that code reads back. The ledger never
holds code. State is the fold of the ledger, checked against the branch
(concept D1).

Only the driver writes to the mend branch, and only after `accept`. Attempt
worktrees are discarded after each attempt (concept D2).

## The trust partition

| Decides — from the lean-mend install | Judged — from the target or an agent |
|---|---|
| the rules in `rules/` | the target's code |
| the probe source | an agent's candidate edit |
| the classifier and the step function | a proposed rule |
| the structural checks and the invariant | |

The target's tree never supplies a rule, a probe or a check. A proposed rule
from an agent runs only through the fixed runner (concept C7).

## The command line

| Command | Effect |
|---|---|
| `lean-mend run <target> --to <toolchain>` | runs the machine from `Idle` to `Done` or `Halted` |
| `lean-mend run <target> --adopt` | accepts a target that another tool already bumped; takes the baseline from the parent commit |
| `lean-mend status <target>` | prints the state from the ledger |
| `lean-mend cards <target>` | lists open cards |
| `lean-mend judge <target> <card> accept\|reject --by <name>` | records a judgment |
| `lean-mend residue <target>` | writes one residue packet per residue site |
| `lean-mend propose <target> <packet> <rule-file>` | runs a proposed rule through the fixed runner |

## Scheduling

The scheduled form is a GitHub Actions workflow in the target. It runs
`lean-update` (or `lean-bump`), then `lean-mend run --adopt` when the build
fails, and opens one pull request with the mend branch, the run report and the
open cards. See [decisions.md](decisions.md), D6.
