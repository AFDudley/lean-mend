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
  * Sched.lean       the memory limit of a run: charges, admission, the probe cap, speculative placement (docs/parallel.md P24)
  * Cause.lean       the cause of a finding: shortest dependency paths, the constant whose own axioms differ, groups, the body diff and its proof check (docs/verification.md § What a card explains)
  Shell/         IO. Parsing at the edge, Lake, git, files, the ledger.
  * Parse.lean       JSON → typed operands, once (concept B2)
  * Target.lean      processes, the probe (embedded by include_str), module graph, per-module lake build, certificate
    Edit.lean        applies a candidate as a byte-range replacement
    Git.lean         the mend branch and attempt worktrees
    Ledger.lean      append and replay
  * Cause.lean       the evidence of the cards: `explain` and `proofs` at each toolchain, lake manifests, `git log -L`
  * Session.lean     the saved session (.lean-mend/session.json), card files, judgments from the ledger
  * Memory.lean      the memory gate: /proc measurement, the admission queue, the optional cgroup tree limit
  * Driver.lean      the composition root (concept A3): `run --adopt`, the dataflow schedule over modules, the ledger
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
* CauseTest.lean the cause of a finding on small graphs and bodies, worked out by hand
* card-cause.sh  Violation cards on tests/fixtures/card-cause: the path and the changed dependency lemma, with its module and revision, at each toolchain
* card-body.sh   Behavior cards on tests/fixtures/card-body: the diff, the commit and its rule, and the proof check
* move.sh        a namespace move with no aliases, including a declaration the app declares under the moved prefix
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
| `decls-batch <list>` | `decls` for every `module<TAB>file` line of the list, from one environment; the shell sends 200 modules per probe process, and runs up to 4 such processes at once (`Target.certificate`; one process holds about 4 GB on EquiVM). Lean cannot import two modules that declare the same name into one environment ("environment already contains", for example `main` of two executables), so the shell runs the probe again without the module that Lean names ("import X failed, environment already contains 'n' from Y"), one run per clash, and reads the moved modules as a list of their own (`Target.declsOf`) |
| `decls <module> <file>` | for each declaration of the built module that the certificate selects: name, kind, statement text and byte range, statement tokens (the atoms and identifiers of the statement region, in source order: the certificate hashes these, `docs/verification.md` § The certificate), body text and byte range, axioms (the set `#print axioms` reports: the edges of `collectAxioms` of Lean v4.29, walked once per probe process with a memo over strongly connected components, `axiomsOf`; per declaration, `collectAxioms` walks the whole closure again, and on EquiVM's `Reasoning.Solc` it costs 70.4 s against 37.3 s on v4.29 and 136.0 s against 50.4 s on v4.33.1, with equal sets on every row). The ranges and tokens come from the file's own commands, parsed with the scopes in effect at each command (`fileCommands`): the probe elaborates the scope commands and the `local` syntax commands, and no declaration or proof. When the probe cannot give the row of a declaration that it selects, it writes an `unread` line that names the declaration, and the shell stops the run with `DeclUnread` |
| `regions <file>` | each declaration command of a file: qualified name, command range, statement and body ranges. The commands are those that the elaboration of the file parsed (`elabCommands`), so the file may fail, but its imports must build. Lean parses each command with the environment after the command before it, so syntax that the same file declares (`macro`, `syntax`, `notation`, `elab`) parses at its later uses |
| `node <file> <offset>…` | for each offset, the syntax nodes that contain it, innermost first: kind and byte range; tactic nodes also carry their tokens with ranges. The commands are those of `regions`. The shell asks at a site's start and its end, because an error such as `unsolved goals` is reported at `by` with a range over the whole block. The list is empty when no command contains the offset: after a parse error, the parser skips to the next command. The site then gets no node, and no rule that needs a node proposes a candidate. Before `elabCommands`, the probe parsed with the imports' environment only, and every site after a use of the file's own syntax got no node (`tests/probe-gap.sh`; EquiVM run 7) |
| `deprecated <module>…` | every `@[deprecated]` declaration in the environment of the modules, with its new name, from `Lean.Linter.deprecatedAttr` |
| `explain <request>` | for the findings of a run (`docs/verification.md` § What a card explains), from one import of the findings' modules: the certificate row of each named declaration (the shape of `decls`), and every constant that the named roots reach over the edges of `axiomsOf`, with its module, its axioms and the constants it uses; a root that the environment does not hold gives a `missing` line; for each module, the `.olean` file that Lean loads, so the shell can name the package that owns it |
| `proofs <file> <start> <stop>…` | for each byte range, the maximal ranges inside it of the proofs: a term whose type is a proposition (term info), and a `by` block whose goals are propositions (tactic info: Lean records a `by` block that way, not as term info). It elaborates the file as `serve` does, so the file's imports must build |
| `goal <file> <pos>` | not built yet: the goal state at a position, from the info tree, for a residue packet |
| `serve` | one JSON request per line of stdin, one JSON reply per line of stdout (`docs/parallel.md` § Level 0, C1-C5). `{"op": "elaborate", "file"}` gives `{"messages"}`: the messages of `lake env lean --json <file>` for the file's current text, from `Lean.Language.Lean.process` with the processor, options, main module name and trust level of `lean --json`. The probe keeps the last elaboration and its text, so the next `elaborate` request on the file elaborates again only from the first changed command. `{"op": "syntax", "file", "offsets"}` gives `{"regions", "nodes"}`: `regions <file>` and `node <file> <offsets>…` from the commands of the kept elaboration when its text is the file's current text; else the request elaborates the current text first |

`Shell/Target.lean` starts one `serve` process per module it mends
(`probeServeStart`), under `lake env lean -M <MiB>` at the probe cap
(`docs/parallel.md` P24). Each reply of `serve` also carries `peakKiB`, the
probe's peak resident size. Each `diagnose` call sends one `elaborate`
request (`probeElaborate`) and, when the module has errors, one `syntax`
request (`probeServe`) on the same text. So every attempt on a module shares
one kept elaboration, and its `syntax` request elaborates nothing, instead of
a new `lean --json` process and a new probe process per call.

The probe process starts in its own session (`setsid`). `probeServeStop`
and `probeServeKill` end its process group, `lake env` and its `lean`
child, with one `SIGKILL`. The stderr reader of the probe does the same at
the text of the `-M` cap, and the first stop of the run ends every live
probe (`docs/parallel.md` § The memory limit, item 7).

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
2. For each failing frontier module, the shell gets the diagnostics of
   `lake env lean --json <file>` from the module's probe `serve` process
   (`elaborate`). This is the second compile of a failing module only.
3. An attempt edits one file in an attempt worktree and sends the next
   `elaborate` request to the same process. Lean elaborates again only from
   the first command that the edit changed. A reverted edit is one more
   change, back to the earlier text.
4. When a module's mend ends with no residue, the shell runs
   `lake build -v +<module>` in the main checkout (`Driver.buildModule`, which
   calls `buildAll`). A blocked module gets the same one-module build when
   every module that it imports builds. Only the modules that the run mends
   or unblocks get one, so these are tens of Lake starts on EquiVM, not
   thousands. One full `lake build -v` at the end checks every module's
   status before the certificate.

Modules are handled in dataflow order (`docs/parallel.md` § Level 2). A
module starts its mend in its own worktree as soon as every module that it
imports builds with its mended text. It does not wait for a module that it
does not import. The driver commits and writes the ledger in the module
topological order, not in completion order. Inside a module's worktree, the
driver by default attempts the next four candidates of the head site at the
same time, each in its own nested worktree (`docs/parallel.md` Level 3,
P25). `--speculate 1` attempts one candidate at a time instead, and it
reverts a rejected candidate by writing back the file's previous bytes.

One memory limit bounds the run (`docs/parallel.md` § The memory limit,
P24): `--max-memory <GiB>`, or else `MemAvailable` at run start minus 16 GiB.
A module or a nested probe starts only when its 10 GiB charge fits beside
the charges of the running work and the driver's measured size, and the
`/proc` measurement of the process tree agrees. Otherwise it waits, with no
probe, until running work ends. When nothing runs, one item starts. A probe
over its cap (`--probe-cap <MiB>`, default 15 GiB) stops the run with the
typed error `CapExceeded` (exit 3). A certificate with no row for a
declaration that it selects stops the run with the typed error `DeclUnread`
(exit 3, `docs/verification.md` § The certificate).

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
| `lean-mend run <target> --adopt [--aliases-from <project>]…` | built: accepts a target that another tool already bumped; the baseline is `HEAD~1` in a detached worktree, `.lean-mend/base`, which the run keeps: a later run at the same `HEAD~1`, with no tracked file changed there, reuses it and its build. The bumped tree and the baseline build at the same time. The baseline certificate is stored in `.lean-mend/base-cert/`, under a key of all its inputs (law LM3); the `baseline` ledger line says whether each was reused (`worktreeReused`, `certificateStored`). Each `--aliases-from` project adds its `@[deprecated]` aliases to the map; `--prepare <cmd>` runs in each new tree before any Lake command there (for example `lake exe cache get`, or a copy of a saved `.lake`; the probe's first `lake env` clones every package into a missing `.lake`); `--targets` limits the Lake targets; `--rules <dir>` loads the rule files; `--annotate-binders` applies the type narrowing of decision D11 (default: report it as a warning). `--follow-definition-changes` lets a statement follow a definition's `match` repair (decision D12; default: report it as a warning). The summary lists the run's warnings |
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
