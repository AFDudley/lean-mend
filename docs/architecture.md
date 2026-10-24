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
  * Graph.lean       module-graph order (topoOrder); a cycle is a refusal
  * Propose.lean     Site × AliasMap → ordered candidates (derived alias rules only); AliasMap.normalize
  * Ops.lean         EditOp on a tactic node → replacement; ruleCandidates; proposeAll (derived, then ratified, then proposed)
  Shell/         IO. Parsing at the edge, Lake, git, files, the ledger.
  * Parse.lean       JSON → typed operands, once (concept B2)
  * Target.lean      processes, the probe (embedded by include_str), module graph, per-module lake build, certificate
    Edit.lean        applies a candidate as a byte-range replacement
    Git.lean         the mend branch and attempt worktrees
    Ledger.lean      append and replay
  * Session.lean     the saved session (.lean-mend/session.json), card files, judgments from the ledger
  * Driver.lean      the composition root (concept A3): `run --adopt`, the level-1 loop, the ledger
* Main.lean      the `lean-mend` executable: `baseline` and `run --adopt`
probe/
  Probe.lean     runs under the TARGET toolchain; writes JSON
rules/
  *.json         ratified rules; proposed rules in rules/proposed/
tests/
* Main.lean      the `lake test` driver
* Tour.lean      the tour of the pure machine
* ClassifyTest.lean  classify on recorded `lean --json` output
* NoSorry.lean   no LeanMend constant depends on sorryAx (the gate runs it)
* baseline.sh    `lean-mend baseline` on the fixture under v4.33.1, intact and broken
* rename.sh      `lean-mend run --adopt` on tests/fixtures/rename, with and without the alias source
* simpset.sh     `lean-mend run --adopt --rules` on tests/fixtures/simpset: three classes repaired, one candidate rejected by the linter condition, one Violation card judged with `lean-mend judge`
* OpsTest.lean   edit operations at their edges, and the rule loader's refusals
* follow.sh      decision D12 on tests/fixtures/follow, a real v4.29.0 → v4.33.1 bump
* binder.sh      decision D11 on tests/fixtures/binder, a real v4.29.0 → v4.33.1 bump: the default warns, `--annotate-binders` narrows
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
| `decls-batch <list>` | `decls` for every `module<TAB>file` line of the list, from one environment; the shell sends 200 modules per probe process |
| `decls <module> <file>` | for each declaration of the built module: name, kind, statement text and byte range, body text and byte range, axioms (by `collectAxioms`, the method of `#print axioms`) |
| `regions <file>` | each declaration command of a file, parsed without elaboration (so it works on a module that fails): qualified name, command range, statement and body ranges. The environment is the file's imports plus the implicit `Init`; notation defined in the same file does not parse |
| `node <file> <offset>…` | for each offset, the syntax nodes that contain it, innermost first: kind and byte range; tactic nodes also carry their tokens with ranges. The shell asks at a site's start and its end, because an error such as `unsolved goals` is reported at `by` with a range over the whole block |
| `deprecated <module>…` | every `@[deprecated]` declaration in the environment of the modules, with its new name, from `Lean.Linter.deprecatedAttr` |
| `goal <file> <pos>` | not built yet: the goal state at a position, from the info tree, for a residue packet |

`Shell/Target.lean` embeds the probe with `include_str`. A change to
`probe/Probe.lean` alone did not rebuild the module in one observed case, so
the binary kept the old probe. `tests/OpsTest.lean` fails if the embedded
text differs from the file. The gate builds from scratch in its container, so
it is not affected.

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

1. The shell runs one `lake build -v` (with `--targets`, if given). Lake prints
   one line per module job, in the same format from v4.29.0 to v4.35.0:
   `Built M` or `Replayed M` is `built`; `✖ … Building M` is `failing`;
   `Ran M` with no build is `blocked`, because an import failed. A module that
   Lake names in no line is not required by the targets, and it is outside the
   run. The first design ran `lake build <module>` once per module; on EquiVM
   (about 10,000 target modules) that is thousands of Lake start-ups.
2. For each failing frontier module, the shell runs
   `lake env lean --json <file>` and parses the diagnostics. This is the second
   compile of a failing module only.
3. An attempt edits one file in an attempt worktree and runs
   `lake build <module>` there. Lake rebuilds only that module, because its
   imports are built.

Modules are handled in graph order (brief item 1). The design attempts
independent frontier modules in parallel, each in its own worktree (concept D3).
The current driver does not do this yet: it attempts one candidate at a time in
the target checkout, and it reverts a rejected candidate by writing back the
file's previous bytes.

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
| `lean-mend run <target> --adopt [--aliases-from <project>]…` | built: accepts a target that another tool already bumped; the baseline is `HEAD~1` in a detached worktree; each `--aliases-from` project adds its `@[deprecated]` aliases to the map; `--prepare <cmd>` runs in both trees before the build (for example `lake exe cache get`); `--targets` limits the Lake targets; `--rules <dir>` loads the rule files; `--annotate-binders` applies the type narrowing of decision D11 (default: report it as a warning). `--follow-definition-changes` lets a statement follow a definition's `match` repair (decision D12; default: report it as a warning). The summary lists the run's warnings |
| `lean-mend status <target>` | prints the state from the ledger |
| `lean-mend cards <target>` | built: lists the cards no judgment has answered, with the path of each card file |
| `lean-mend judge <target> <card> accept\|reject --by <name>` | built: records the judgment in the ledger and steps the machine on the saved session; a rejected Behavior card does not yet revert its patch |
| `lean-mend residue <target>` | writes one residue packet per residue site |
| `lean-mend propose <target> <packet> <rule-file>` | runs a proposed rule through the fixed runner |

## Scheduling

The scheduled form is a GitHub Actions workflow in the target. It runs
`lean-update` (or `lean-bump`), then `lean-mend run --adopt` when the build
fails, and opens one pull request with the mend branch, the run report and the
open cards. See [decisions.md](decisions.md), D6.
