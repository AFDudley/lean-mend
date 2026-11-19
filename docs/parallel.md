# Parallel lean-mend

This document is the design contract for a parallel lean-mend. Exophial
workers implement it from pebbles that quote its decisions. If this document
and the Lean code disagree, the Lean code is correct and this document is
stale.

## The problem

One EVMLean run (v4.29.0 → v4.33.1) takes about 3 hours. Run 21 took 11738 s
for 333 attempts and 147 commits. The sequential driver attempts one candidate
at one site at one module at a time (`LeanMend/Shell/Driver.lean`, `loop`).

One attempt starts three processes. `lake env lean --json` elaborates the
module. The probe then runs two times, for `regions` and for `node`, and each
run imports the module's imports again. § The cost of one attempt gives the
measured numbers. The two probe runs take about 80 % of the attempt time. The
elaboration of the unchanged commands before the edit takes most of the
remainder.

This design first removes the repeated work inside one attempt (Level 0). It
then adds three kinds of parallelism and one measure change. Each level keeps
the mend branch deterministic. The functional core stays pure. The reuse and
the concurrency live in the shell. The Core decides acceptance.

Three rules hold for every level:

1. The Core decides and orders. The shell only gathers observations and
   applies the Core's decision.
2. The determinism anchor is the commit order and the ledger order. The driver
   writes both in the canonical sequential order, not in completion order.
3. Termination stays a theorem. No level adds a retry cap, a timeout control,
   or a fallback.

## Measured numbers

The host ran these commands on 2026-10-25. An EVMLean mend run shared the
machine. The state of that run changed the load average between measures. Each
number below names the command that produced it.

| Fact | Command | Value |
|---|---|---|
| Logical cores | `nproc` | 32 |
| Total memory | `free -g` | 187 GiB |
| Available memory | `free -g` | 14–17 GiB (during the shared run) |
| Swap | `free -g` | 0 GiB |
| Load average at start | `cat /proc/loadavg` | 25.92 (1-minute) |
| Load average at the RSS measure | `cat /proc/loadavg` | 4.17 before, 4.72 after (1-minute) |

The clone built under the target toolchain v4.33.1:

```
git clone ~/code/git_puller/repos/EVMLean <dir>
git -C <dir> checkout bcca6b1
export PATH="$HOME/.elan/bin:$PATH"
lake exe cache get      # 43.5 s, 8689 cached files
lake build              # 507.8 s, 3177 jobs
```

One rebuild of the largest theorem module:

```
/usr/bin/time -v lake env lean --json Ethereum/Theory/ReturnDataBound.lean
```

| Fact | Value |
|---|---|
| Peak resident set size | 2318732 KiB ≈ 2.21 GiB |
| Elapsed wall time | 26.45 s (loaded machine) |
| User time | 46.67 s |
| System time | 21.18 s |
| CPU share | 256 % (about 2.5 cores inside one `lean` process) |
| File size | 186009 bytes, 4089 lines |
| theorem or lemma declarations | 156 |
| def, abbrev or instance declarations | 4 |

Disk of the built clone:

| Fact | Command | Value |
|---|---|---|
| Whole build | `du -sh .lake` | 3.0 GiB |
| Dependency build | `du -sh .lake/packages` | 2.9 GiB |
| Root package build | `du -sh .lake/build` | 38 MiB |
| Source tree | `du -sh --exclude=.lake --exclude=.git .` | 690 KiB |
| Git store | `du -sh .git` | 20 MiB |
| Target module count | `find -name '*.lean'` | 60 |

Worktree copy cost:

| Fact | Command | Value |
|---|---|---|
| Hardlink copy of `.lake` | `cp -al .lake <dir>` | 3.89 s, 0 extra data blocks |
| Reflink copy | `cp --reflink=always` | not supported (zfs 2.2.2, block clone off) |

These numbers set the concurrency budget. One large-file `lean` process needs
about 2.2 GiB and about 2.5 cores. Swap is 0, so an overcommit kills a process
with the OOM killer. The dependency build is 2.9 GiB and never rebuilds during
a mend. The root build is only 38 MiB. So an attempt worktree shares the
dependency build and keeps a small root build of its own.

### The cost of one attempt

The host ran these commands on 2026-10-27 in the EVMLean target
`.scratch/mend-target`, on branch `lean-mend/mend`. Other work shared the
machine. The 1-minute load average was 30 to 40. The probe is
`probe/Probe.lean` at `e357c63`, the version of run 21. `HEAD` makes the same
calls (`LeanMend/Shell/Target.lean`, `diagnose`).

| Step | Command | Wall time |
|---|---|---|
| Elaborate `ReturnDataBound.lean` (4084 lines) | `lake env lean --json <file>` | 11.9–13.2 s |
| Elaborate its first 2362 lines | the same, on a copy cut after line 2362 | 9.4 s |
| Elaborate its first 1200 lines | the same, on a copy cut after line 1200 | 6.3 s |
| Elaborate its import header only | the same, on a copy with the `import` lines only | 5.2 s |
| Probe `regions` on `ReturnDataBound.lean` | `lake env lean --run .lean-mend/Probe.lean regions <file>` | 24.2–45.9 s |
| Probe `node` on `ReturnDataBound.lean` | `lake env lean --run .lean-mend/Probe.lean node <file> <offset>` | 22.9–25.8 s |
| Probe `regions` on `NoOutOfFuel.lean` | `lake env lean --run .lean-mend/Probe.lean regions <file>` | 21.0 s |
| Probe with no command | `lake env lean --run .lean-mend/Probe.lean` | 2.7–2.9 s |

`diagnose` runs the elaboration one time and the probe two times for each
attempt. So one attempt on `ReturnDataBound.lean` takes about 60 s, and the
two probe runs take about 47 s of it. Each probe run calls `importModules` on
the file's imports and parses the whole file. A probe run on the small
`NoOutOfFuel.lean` also takes 21 s. So the import step, not the parse, sets
most of the probe time. The probe interprets its own code (`lean --run`) and
imports with `loadExts := true`. The elaboration loads the same imports in
about 5 s. This document does not explain the difference.

Run 21's mend branch has 147 commits. The mean time between two commits is
75 s (10993 s over 146 intervals). The ledger has no time stamps, so it does
not give the time of each attempt. The measures above ran at a higher load than
run 21, so their absolute times are higher than run 21's. Their ratios are the
basis of Level 0. The earlier `ReturnDataBound` measure in this section
(26.45 s) is from a different load.

## Level 0: one probe process per module, and reuse of the unchanged commands

### Mechanism

The shell starts one probe process for each module that it mends (C1). The
process reads requests from its standard input. One request names one file
version and a list of byte offsets. The reply holds the declaration regions
and the nodes at the offsets (C3). The probe reads them from the commands of
its kept elaboration of the same text (the `elaborate` request below), so
syntax that the file declares parses at its later uses. Lean's elaboration
imports the header again only when the header differs from the header of the
kept elaboration (C2).

The same probe process also gives the diagnostics of an attempt (C4). It
elaborates the module file and keeps the elaborated state after each command.
The shell sends each candidate's text as a new request. The probe compares the
new text with the previous text, and it elaborates again only from the first
changed command. The commands before the edit keep their state. The reply
holds the messages of the new text, in the form and order of `lean --json`
(C5).

Two mechanisms can keep the elaborated state: (a) a client of
`lake env lean --server`, with `didOpen` and `didChange`, or (b) incremental
elaboration inside the probe `serve` process. The design uses (b), for four
reasons:

1. The probe process already exists, one for each module (S0a), and it
   already holds the module's imports. A Lean server is a second process type
   for each module, and it imports the module's imports a second time.
2. The server and `lean --json` call the same language processor,
   `Lean.Language.Lean.process`. The probe calls it too, with the previous
   snapshot tree as `old?`, and with the main module name, trust level and
   options of `lean --json`. One option differs: `internal.cmdlineSnapshots`
   is off, as in the server. When it is on, Lean discards the syntax of each
   command, and it cannot find the unchanged commands. The probe writes each
   message with `Message.toJson` in the tree order of
   `Language.SnapshotTree.runAndReport`, as `lean --json` does, and it stops at
   `maxErrors` errors, as `lean --json` does.
3. A server file worker gets its imports and options from `lake setup-file`.
   That command applies the lakefile's `leanOptions`, which
   `lake env lean --json` does not, and it builds missing imports. An attempt
   worktree shares the main checkout's build (P18), so a build there writes
   the shared build.
4. A server diagnostic carries no message kind for a linter warning, and its
   columns count UTF-16 code units. `diagnose` reads the kind (`linter.*`), and
   `lean --json` columns count code points.

### The Core change

None. The Core receives the same observations as before. Only the way the
shell computes an observation changes.

### The Shell change

`probe/Probe.lean` gets a `serve` command. It reads one JSON request for each
line and writes one JSON reply for each line. A `syntax` request gives the
regions and the nodes. An `elaborate` request gives the messages of the file's
current text. `LeanMend/Shell/Target.lean` gets a probe session (start,
request, stop). `diagnose` makes one `elaborate` request in place of one
`lean --json` run, and one `syntax` request in place of two probe runs.
`diagnose` and `attemptOne` read the diagnostics from that session. A revert
is a change back to the previous text: the next request sends that text.

### The proof obligations

None in Lean, because the Core does not change. The equality of the two
diagnostic sources is a property of Lean, not of the Core. C5 states it. Slice
S0b checks it on fixtures, and the operator checks it on EVMLean.

### The determinism argument

The probe reply for one file version is a function of the file text and the
imports only: Lean parses and elaborates the same text the same way. So a
long-lived probe process gives the same reply as a new one.
The probe's elaboration gives the same messages as `lean --json` for the same
text (C5). So each observation is the same as before, and the Core makes the
same decisions in the same order.

### The expected speedup with its basis

§ The cost of one attempt gives the basis. One probe process per module
removes about 47 s of a 60 s attempt on `ReturnDataBound.lean`. The probe
import then occurs one time for each module. The reuse of the unchanged
commands removes the elaboration of the commands before the edit. At line 2354
of `ReturnDataBound.lean`, that is about 9 s of 13 s. The remaining cost is the
elaboration from the edit to the end of the file.

`tests/server-diag.sh` measured the probe changes in the gate run of
2026-11-05, with a 1-minute load average of about 4.3. On a generated module
of 200 theorems, an edit in theorem 195 took 146 ms. `lake env lean --json` on
the same text took 2392 ms. On the five changes of
`tests/fixtures/server-diag`, one change took 5 to 183 ms. The peak resident
size of the probe process was 1299516 KiB (1.24 GiB) for the small module and
1491540 KiB (1.42 GiB) for the 200-theorem module. In the same gate run,
`tests/probe-serve.sh` measured 1294248 KiB for a probe process that
elaborates nothing. So the probe's own start (`import Lean`) sets most of the
size, and the kept elaboration of 200 theorems adds about 0.18 GiB. The
operator measures the change time on a large EquiVM module, for example
`Examples.StringStoreLite.Getters`, and records it in this section.

## Level 1: prefetch across declarations in one module

### Mechanism

A theorem body is invisible to every other declaration. Lean checks each
declaration separately. Lean adds a failed declaration with `sorry` and still
gives later declarations the failed declaration's type. So the result of a
theorem-body edit depends only on the text of that declaration and on the
declarations before it. Of an earlier theorem or lemma, only its statement
counts.

The shell attempts the first candidate of each eligible theorem site at the
same time, each in its own attempt (P4). A site is eligible when it is in a
theorem or lemma body region (P2), it is the earliest open site of its
declaration (P6), and its candidate is not a D12 combined candidate (P7). The
shell keeps each result: the diagnostics inside the edited declaration, with
positions relative to the start of the declaration. A result has a key (P5).
The key is the declaration index, the edited declaration text, the statements
of the earlier declarations, and the bodies of the earlier declarations that
are not theorems or lemmas.

The Core still decides only the head site, with the existing `Mending.step`
(P3). When the head candidate has a result with a valid key, the shell makes
the module observation from that result and from the current diagnostics of
every other declaration. It does not attempt the candidate again (P20). When no
valid result exists, the shell attempts the candidate as before. Example: a
module with 22 `NoOutOfFuel` sites and one rule needs 22 attempts at the same
time, then 22 decisions with no further attempt.

### The Core change

`Mending.batch : Mending → List (Nat × Candidate)` selects the head candidate
of each eligible, distinct theorem declaration, with the site's index. The
branch `worker/lea-fc0` (commit `6f9984c`) has it, with `batch_distinct` and
`batch_bodyOnly` proved. `Mending.step` does not change. The Core has no batch
step.

### The Shell change

`LeanMend/Shell/Driver.lean` calls `Mending.batch` when a module starts and
after each accepted edit. It attempts the selected candidates that have no
valid result, within the worker budget (P17). It keeps the results in a table
for the module. Before an attempt at the head, it looks up the table. A hit
gives the observation with no attempt. The ledger records each prefetched
attempt and each use of a kept result. The run option `--prefetch <n>` sets
the prefetch width. `--prefetch 0` attempts only at the head, as before.

### The proof obligations

| Theorem | Statement |
|---|---|
| `Mending.batch_distinct` | the sites that `Mending.batch` returns have pairwise distinct declarations |
| `Mending.batch_bodyOnly` | every candidate from `Mending.batch` targets a theorem or lemma body region |

The Core decides with `Mending.step` only. So `Mending.step_measure` and
`branchSound` apply to every commit without change. Termination needs no new
proof.

An earlier design decided a whole batch in one Core step (`Mending.stepBatch`).
Its measure theorem `stepBatch_measure` is false for the five-tuple measure. A
batch can reject the head candidate and accept a later site that exposes two
errors. Then the open-site count rises, and the head does not move. This
counterexample was derived by hand. The prefetch design has no batch step, so
it does not need that theorem.

### The determinism argument

A kept result with a valid key equals the result of the same attempt at the
time the Core consumes it. The reason is theorem-body independence and the
key. An edit to the body of theorem A never changes whether theorem B
elaborates, because B uses only the type of A. The key holds the text of B and
every earlier text that B can depend on. A change to any of them makes the key
not valid, and the shell attempts again. The Core consumes the observations in
the order of the sequential run. So the accepted candidates and the commit
order match the sequential run.

This independence is a property of Lean's elaborator, not of the Core. The
Core cannot prove it. The design states it, and the prefetch fixture checks it
on a real module (slice S2b).

### The expected speedup with its basis

The prefetch makes the first attempts of a module's theorem sites parallel. A
module whose M theorem sites each pass with their first candidate needs about
one attempt time instead of M, within the worker budget. `ReturnDataBound.lean`
has 156 theorem or lemma bodies and 4 defs, so the prefetch applies to almost
every site. A site whose first candidate fails attempts its later candidates
at the head, as before.

## Level 2: dataflow across modules

### Mechanism

A module can mend when it fails and every module that it imports builds. A
module starts its mend as soon as every module that it imports builds with
its mended text (P8). It mends in its own attempt worktree. It does not wait
for a module that it does not import. Two modules that mend at the same time
never import each other: a module that mends fails, and a mend starts only
when every import builds.

When a mend ends with no residue, the driver writes the mended file into the
main checkout and builds that one module, `lake build +<module>` (P13). This
step makes no commit and writes no ledger line. Then the modules that import
it can start. A blocked module builds one time, when every module that it
imports builds (P21). Its result is `built` or `failing`. A `failing` result
starts its mend. A mend that ends with residue does not build. The module is
`residual`, so no module that imports it starts. The sequential run and the
wave run (the earlier design, below) did the same: a module that imports a
residual module stays blocked and is in the residue list.

The driver commits in the canonical order (P10). The canonical order is the
module topological order of the run (`topoOrder`). The next module of that
order is the head of `ready` on the machine's own statuses. The driver
replays a module, that is, it writes the module's ledger lines and commits,
only when the results of that module are there. So a module commits only
after every module before it in the canonical order. The ledger has the same
order (P12).

One full `lake build` runs at the end, before the certificate. The machine
checks every module's status in it (`Settled`).

An earlier design mended in waves. A wave was every frontier module of the
moment. When the wave finished, the driver rebuilt the whole target and
computed the next wave. EquiVM run 6 (lean-mend `05ef9913`) showed the cost.
In wave 2, 37 modules finished in about 1 h. `Examples.StringStoreLite.Getters`
(6555 lines, 230 theorems) took more than 2 h 20 min. Every module of the next
wave waited for `Getters`, also the modules that do not import it.

### The Core change

- `ready mods st` (`LeanMend/Core/Run.lean`): every open module whose imports
  all build, in `mods` order. A `failing` one can mend. A `blocked` one can
  build.
- `RunObs.moduleBuild module status`, with `RunState.moduleBuilt`. In `built`,
  a ready `blocked` module takes the status `built` or `failing`. A module
  that the run mended with no residue must report `built`. Any other
  observation halts.
- `importClosure mods n` (`LeanMend/Core/Graph.lean`): every module that `n`
  imports, directly or through other modules (P22).

`RunState.mending` holds a fleet, `Fleet := List Mending`, with a
well-formedness field that the modules are distinct. The driver replays one
module at a time, so its ledger fills the fleet with one member at a time.

### The Shell change

`LeanMend/Shell/Driver.lean`, `dataflow`. `launch` starts a task for every
module that `ready` names on the live statuses: a build for a blocked module,
a mend for a failing module. `settle` takes the result of each task when the
task ends. `advance` replays every result that the canonical order can take.

The worktree of a module starts from a commit that `git stash create` makes
of the main checkout. That commit holds `HEAD` and the mended text of every
module whose mend ended but is not committed. So the worktree holds the text
of every module that the module imports, as built. Each worktree symlinks the
shared build directory (P18).

The driver commits through the git index (P23). It applies each accepted
candidate to the module's text in memory, writes the blob with
`git hash-object -w`, puts it in the index with `git update-index --cacheinfo`,
and runs `git commit`. The working tree file changes one time only, when the
mend ends. A `lake build` of a module that imports it reads that file at any
time. A commit through the working tree would show it a text between two
commits. Only the driver writes the mend branch, so the branch has one writer
(P11).

`buildAll` stays the only writer of the build output (P18). `buildModule`
calls it with the one target `+<module>`.

### The proof obligations

| Theorem | Statement |
|---|---|
| `frontier_pairwise_indep` | for m and n in `frontier mods st` with m ≠ n, n is not in m's import list |
| `ready_imports_built` | a ready module is open, and every module that it imports builds |
| `frontier_sub_ready` | every frontier module is ready |
| `RunState.moduleBuilt_settled` | a `moduleBuild` keeps every closed module as it was, so `openCount_settled` applies |
| `blockedCount_moduleBuilt` | a `moduleBuild` that unblocks a module lowers `blockedCount` |
| `openCount_settled` | a settled rebuild never raises `openCount` (unchanged) |
| `Fleet.step_wf` | routing an observation to its module keeps the fleet's distinctness invariant |

The modules that mend at the same time are frontier modules of the live
statuses. So `frontier_pairwise_indep` shows that they do not import each
other. The level-1 measure is the pair (`openCount`, `blockedCount`), in
lexicographic order. `mended` lowers `openCount` (`openCount_finish`). A
`moduleBuild` that unblocks a module does not raise `openCount`, and it lowers
`blockedCount`.

### The determinism argument

The mended text of a module is a function of three inputs: its own text, the
mended text of the modules that it imports, and its followed-rule snapshot
(P22). Every module that it imports ends before it starts. So each input is
fixed when it starts, and the completion order of other modules does not
change it. The driver commits and writes the ledger in the canonical order, so
neither depends on the completion order.

The canonical order is the order of the sequential run. The sequential run
mends the first frontier module in topological order, rebuilds, and then
takes the next. The module it takes is always the first open module in
topological order whose imports all build. That module is the head of
`ready`.

The wave run committed in wave order: every module of wave 1, then every
module of wave 2. That order is different from the canonical order when a
module of a later wave comes before a module of an earlier wave in the
topological order. The final tree is the same, but the commit order and the
ledger order are different.

The followed-rule snapshot (decision D12) holds the body rules that the
modules a module imports accepted (P22). The wave run gave a module the body
rules of every earlier wave, also of modules that it does not import. A
module does not wait for such a module, so their rules are not known when it
starts. With `--follow-definition-changes`, a statement can thus keep its
text where the wave run followed a rule from a module that it does not
import. Without the flag, the snapshot changes only the warnings, not the
tree.

One case does not hold by construction. Parallel builds raise host contention,
so a `wallclock` timeout is more likely. A `wallclock` site is rebuilt alone,
with no other build running, so its verdict is the quiescent verdict (P19). If
the quiescent rebuild still times out, the run halts with `HostTimeout`. It
never commits a different patch. So the mend branch is deterministic, and the
only parallel-specific outcome is a controlled halt, which is acceptable. The
`heartbeat` class is deterministic (Lean counts its own allocations), so
parallelism does not change a heartbeat verdict.

### The expected speedup with its basis

The parallel width is bounded by the worker budget. The worker budget is
about 7 on a shared machine (17 GiB available ÷ 2.2 GiB per process) and
about 12 on a free machine (32 cores ÷ 2.5 cores per process). The floor is
the critical path: the longest chain of modules that import each other, with
the mend time of each module and one `lake build +<module>` for each. The wave
run added a wait for the slowest module of each wave, and one full rebuild
between two waves. The dataflow run removes both. It runs one full build at
the end only.

On `tests/fixtures/dataflow`, `Dep` imports `Fast` only. `Dep`'s first
attempt started 7.4 s after `Fast`'s mend ended and 19.9 s before `Slow`'s
mend ended (`tests/dataflow.sh`, 2026-11-05). The wave binary (`integrated`
at `05ef9913`) started it 23.7 s after `Slow`'s mend ended.

## Level 3: speculation across the candidates of one site

### Mechanism

A stubborn site needs several candidates before one passes. The shell attempts
the next N head candidates of that site at the same time, each in its own
worktree (P14). The Core accepts the first candidate that passes in rule order,
not the first worktree that finishes (P15). The shell discards every
speculative result after the accepted candidate in rule order (P16). The
default width is 4 (P25). `--speculate 1` attempts one candidate at a time.

### The Core change

`Mending.speculate : Mending → Nat → List Candidate` returns the next N head
candidates. The acceptance stays `Mending.step`. The Core feeds the speculative
verdicts to `step` in rule order: a reject for each earlier candidate that
failed, then an accept at the first that passed.

### The Shell change

The driver asks `Mending.speculate m N` for the head site. It applies each
candidate in its own worktree, rebuilds each, and collects the verdicts. It
then calls `Mending.step` with the verdicts in rule order and commits the first
accepted candidate. It discards the other worktrees.

### The proof obligations

| Theorem | Statement |
|---|---|
| `Mending.speculate_prefix` | `speculate m n` is a prefix of the head site's candidate list |
| (reuse) `Mending.step_measure` | each consumed verdict is one `step`, so the measure falls |

`speculate_prefix` shows the speculative order is the rule order. So the Core
accepts the same candidate as the sequential run.

### The determinism argument

The committed candidate is the first in rule order that passes. This is the
sequential choice. A later candidate that finishes first and also passes is
discarded. So the commit is identical to the sequential run, byte for byte.

### The expected speedup with its basis

A site whose accepted candidate sits at rule position k needs k rebuilds in the
sequential run. Speculation with N ≥ k cuts the wall time of that site to 1
rebuild, at a cost of k parallel workers. The mean k over EVMLean sites is
small, because the first candidate is usually a named lemma that holds. So
speculation mainly shortens the critical path, that is a deep chain with a
narrow frontier where levels 1 and 2 give little. Its cost is wasted rebuilds.

The default width of 4 covers every candidate of a site with up to four
candidates in one round. In run 21's ledger, the first diagnosed site of
`Ethereum.UInt256` had 4 candidates. One round of width 4 on
`ReturnDataBound.lean` holds about 4 × 2.2 GiB of Lean processes. Until the
scheduler (S5, P17) exists, nothing caps the product of the wave width and the
speculative width. A run on a host with less free memory sets a lower width.

## The combined scheduler

Level 0 makes each attempt shorter. The three other levels attack three serial
axes. Level 2 runs independent modules at once. Level 1 attempts many sites of
one module at once. Level 3 attempts many candidates of one site at once. One
memory limit serves all three (P17, P24, § The memory limit). Each probe
process, a module's own or a nested one of a speculative round, is one work
item, and each module build is one work item.

The parallel speedup is bounded by the worker budget (about 7 to 12) and by the
longest module chain that cannot run in parallel. A realistic range is 4× to
8×, from the measured budget and the EVMLean graph shape. The design does not
promise more, because the import depth sets a floor that no level removes. The
Level 0 factor is separate, because it shortens each attempt.

## "Any number after" exposure with AST coordinates

This item changes `Mending.measure` and `Mending.step`. The parallel levels use
the same measure. Implement this item first (slice S1).

### The problem

The current Core accepts an edit when the module's error count falls, or when
the count is unchanged and the edit exposed one later error in the same
declaration. The operator wants an edit accepted when it exposes any number of
later errors in the same declaration.

A first attempt used the byte distance from the earliest open error to the end
of the file as the first measure component. EVMLean run 20 refuted it. The
`valCompare` edit at `Semantics` 1040 (declaration Θ) added `.val` bytes. So
the distance of site 288 (declaration `create`, earlier) to the end of the
file grew. The Core then rejected a correct edit. The shell also reports sites
in Lean's message order, not source order. Site 1040 was the head while site
288 was open.

### Mechanism

A position is an AST coordinate. The coordinate is the pair (declaration index
in source order, bytes from the error to the end of that declaration) (X1). D10
fixes the declaration set. Lean checks declarations in source order. So an edit
in one declaration never changes an error in an earlier declaration (X6). The
coordinate of site 288 does not move when the shell edits declaration Θ.

The Core sorts the open sites by this coordinate (X2). The head site is the
earliest error. An edit is accepted when the earliest open position moves
strictly toward the end of the file (X3). An edit is rejected when it leaves or
adds an error earlier than the old head (X4). "Any number after" is free: the
error count may rise, and the head still moves later, so the Core accepts.

### The Core change

`Site.declIndex : Nat` and `Site.reach : Nat` give the coordinate. `reach` is
the byte count from the error start to the end of the declaration's command.
The shell fills both from the probe's source-order `regions`.

```
def Site.earlier (a b : Site) : Bool :=
  a.declIndex < b.declIndex || (a.declIndex == b.declIndex && b.reach < a.reach)
```

`Mending.sites` is kept sorted by `Site.earlier`, so the head is the earliest.
`Mending` gains `decls : Nat`, the module's declaration count, which D10 fixes.

The measure is a five-tuple on `Nat × Nat × Nat × Nat × Nat`, ordered by
`Prod.Lex` (X5, X8):

```
def Mending.measure (m : Mending) : Nat × Nat × Nat × Nat × Nat :=
  match m.sites with
  | [] => (0, 0, 0, 0, 0)
  | o :: _ =>
    (m.decls - 1 - o.site.declIndex,   -- declarations after the head
     o.site.reach,                     -- head reach, bytes to the declaration end
     m.sites.length,                   -- open sites
     o.candidates.length,              -- head candidates left
     (o.candidates.head?.map (·.replacement.length)).getD 0)  -- head replacement length
```

Component 1 falls when the head moves to a later declaration. Component 2 falls
when the head moves later inside one declaration. Component 3 falls when the
head site becomes residue and the next head has the same position: Lean can
report two errors at one position, and then components 1 and 2 do not change.
Component 4 falls on a reject. Component 5 falls on a cleaning by Lean's hint.
The measure uses Lean core `Prod.Lex` only. It is not a multiset order.
`Accepted.progress` becomes "the earliest open position advanced".
`branchSound` is re-proved over the new field.

A first design had four components, without the open-site count. The first S1
worker (lea-e1b) found that a give-up does not lower it when the next head has
the same position, and added component 3.

### The D12 combined candidate

A `--follow-definition-changes` edit fixes a body error. It can leave an error
in the statement. The statement is earlier in the same declaration. A body-only
edit then moves the head back, and the Core rejects it. So the body edit and
its statement follow must be one candidate (X7).

The proposer in `LeanMend/Core/Ops.lean` detects a declaration where a body
rule matches and the same pattern occurs in the statement. Under
`--follow-definition-changes`, it emits one `Candidate`. The candidate spans
from the statement start to the body end. The `replacement` applies the same
transform to both the statement occurrence and the body occurrence. The
`changed` field lists the two edited spans, so the linter check reads only the
changed bytes. The `target` is `EditTarget.followStatement decl`, so the driver
records the declaration in `followedDecls`. The declaration then enters
`after.followed`, so `NoHarm` part 1 holds. The probe supplies the statement
and body region text, so the proposer builds the combined replacement purely.
One atomic candidate gives one rebuild.

### How this interacts with the prefetch

The Core still decides one head at a time, so the five-tuple measure and its
theorems apply without change. The prefetch only supplies observations before
the Core needs them.

A D12 combined candidate changes a statement. A later declaration can depend on
that statement's type. Proof irrelevance does not protect a later declaration
from a statement change. So the prefetch excludes a D12 combined candidate
(P7). The module attempts that candidate at the head, as before.

### The proof obligations

| Theorem | Statement |
|---|---|
| `Site.earlier_total` | `Site.earlier` is a decidable, total, strict order on sites |
| `Mending.sort_head_earliest` | the head of the sorted sites is `earlier`-minimal |
| `Mending.accept_advances` | an accepted step makes the head coordinate strictly later, so components 1 and 2 fall lexicographically |
| `Mending.step_measure` | every successful `Mending.step` lowers `Mending.measure` lexicographically (re-proved) |
| `branchSound` | every mend-branch patch carries its progress, clean and lint-free evidence (re-proved over the new `progress`) |

### The determinism argument

The Core sorts the sites, so the head does not depend on the shell's message
order. The coordinate of an earlier declaration is stable under a later edit,
so the measure is monotone. The same input gives the same accept or reject at
each site, in the same order. So the mend branch matches across runs, byte for
byte.

## The memory limit

### The problem

EquiVM run 7 (lean-mend `7319bd3b`) nearly exhausted the host. The sampler
log `EquiVM/.scratch/mend-cache/run7-mem.log` (one line every 60 s) shows the
probe processes at 115.9 GB at 22:35:59, with 26 GB free, and 6 GB free at
22:51:10. The host has 187 GiB and no swap, so an exhausted host means that
the OOM killer stops a process. The dataflow schedule started every ready
module at once, and nothing bounded the total.

The sampler counted 58 probe processes for 29 modules. One probe session is
two processes: `lake env` (about 0.06 GiB private memory) and its `lean`
child. With `--speculate 1` (run 7), one module holds one session, from its
first diagnose to the end of its mend (`planSession`). The code before this
change gave a speculative round of width `w` one nested session for each
candidate, so one module held `1 + w` sessions during a round.

### The design

The design follows Bazel's local resources
(<https://jmmv.dev/2019/12/bazel-local-resources.html>): each running work
item is charged its estimated peak, and new work starts only when the
charges fit the limit (`Core/Sched.lean`, `Shell/Memory.lean`).

1. The limit is `--max-memory <GiB>`. With no flag, the limit is
   `MemAvailable` of `/proc/meminfo` at run start minus a reserve of 16 GiB.
2. Each work item is charged 10 GiB (`workEstimate`). A work item is a
   module probe, a nested probe of a speculative round, or a module build.
3. A module starts its probe only when two totals fit the limit. The charged
   total is the driver's measured size plus the charges of the running work
   plus the new charge. The measured total is the measured private memory of
   the driver and all its descendants, plus the part of the charge that each
   live probe can still grow into, plus the new charge. `/proc/<pid>/status`
   gives `RssAnon` plus `RssShmem`. File pages do not count, because the
   processes share the `.olean` pages and the kernel can drop them.
4. When nothing runs, one item starts even if it does not fit (as Bazel's
   `--allow_one_action_on_resource_unavailable`). No running work can end and
   free memory, so a wait would never end.
5. A module that does not fit waits in a queue, in request order, so the
   modules get their probes in canonical order. It holds no probe and no
   thread: its task starts when the gate resolves its promise
   (`IO.mapTask`). The gate checks the queue when a probe stops, when a build
   ends, and when the replay frees plans. There is no poll, no sleep and no
   timeout.
6. A speculative round of width `w` runs its first candidate on its module's
   own probe. It asks for `w - 1` other probes with no wait, and runs each
   candidate that got none on its module's own probe, in rule order
   (`roundPlacement`). So a round never waits for memory while it holds a
   probe, and it progresses for every limit. With a limit below one charge,
   a round of width 3 runs as a `--speculate 1` run does.
7. Each probe runs under `lake env lean -M <MiB>`, at the charge times 3/2,
   15 GiB (`probeCap`). `lean -M` calls `Lean.Internal.setMaxMemory`
   (`src/lean/Lean/Shell.lean`) before `runMain` in v4.29.0, v4.33.1 and
   v4.35.0. The probe cannot call it itself: in v4.35.0 it is private
   (`l___private_Lean_Shell_0__Lean_Internal_setMaxMemory`), and the
   interpreter does not bind a local `@[extern]`. Over the cap, the Lean
   runtime (`check_memory`) stops the probe with "excessive memory
   consumption detected". The driver then stops the run with the typed
   error `CapExceeded` (exit 3, ledger line `capExceeded`), which names the
   module, the cap and the probe's peak at its last reply. There is no
   retry.

   The driver reads each probe's stderr in a task. At the cap text, that
   task ends the probe at once, records `CapExceeded`, and stops the run. It
   does not wait for the probe to exit. On 2026-11-06 a run with
   `import Lean` fixtures saw probes that wrote the cap text, and the run
   then made no progress for 3600 s. Each probe starts in its own session
   (`setsid`), so one `SIGKILL` to its process group ends `lake env` and its
   `lean` child. Both hold the probe's stdout, so the request that waits for
   a reply reads end of file. `IO.Process.Child.takeStdin` loses the
   `setsid` flag of the child in v4.35.0, so the session keeps the child
   with its stdin, and the normal stop of a probe is the same kill.

   The first stop of the run, `CapExceeded` or any other error, ends every
   live probe and refuses every probe request that waits (`Gate.stop`).
   Each task of the schedule then ends. The driver waits for every task,
   removes the mend worktrees, and exits with the first stop
   (`stopSchedule`). Before this, the driver left the schedule at the first
   error and did not wait. The exit of a compiled Lean program waits for
   its dedicated tasks, so a task that waited for a live probe held the
   run. `tests/cap-stop.sh` checks the stop with a probe that writes the cap
   text and does not exit.
8. The ledger starts with a `memoryLimit` line: the limit and its inputs,
   the charge, the cap, the tree limit and the tree's measured size. Each
   `probeStart` line holds the charged and the measured totals, the tree and
   driver sizes, and the live probe and build counts at its admission. Each
   `probeStop` line holds the probe's peak.

The kernel limits that the design does not use, with the reason:

- `RLIMIT_RSS` has no effect on Linux (man7 getrlimit(2),
  <https://man7.org/linux/man-pages/man2/getrlimit.2.html>).
- `RLIMIT_AS` and `RLIMIT_DATA` count reserved virtual memory. On run 7 a
  probe `lean` had `VmData` 57 to 110 GB at a resident size of 5.4 to 8.6 GB.
  On kelce on 2026-11-06, `prlimit --data` at 2, 4 and 8 GiB stopped a
  fixture probe at start ("failed to create thread"), at a resident size
  below 0.9 GiB. `ulimit -v` at 4 GiB stopped `lean` the same way.
- A cgroup v2 `memory.max` on the whole tree needs the driver's own cgroup
  to be writable and to have the memory controller (docs.kernel.org
  cgroup-v2, Delegation,
  <https://docs.kernel.org/admin-guide/cgroup-v2.html#delegation>). The
  driver checks it at start (`setupTreeLimit`). On kelce a run from an SSH
  session is in `/system.slice/ssh.service`, which root owns, so the
  ledger records `"treeLimit": {"mechanism": "none", …}` and the run
  continues. In a delegated cgroup the driver moves itself into a child
  cgroup with `memory.max` at the limit.

### The data and the decisions

The numbers of P24, from run 7 (`ps` and `/proc/<pid>/status` of the live
probes, read-only, on 2026-11-05 and 2026-11-06):

| Module | Bytes | Declarations | `VmHWM` of the probe `lean` |
|---|---|---|---|
| `Examples.ERC20.TransferFrom` | 133833 | 149 | 10302488 KiB |
| `Examples.Ballot.Delegate` | 227729 | 250 | 9047944 KiB |
| `Examples.BlindAuction.Reveal.Common` | 201108 | 131 | 7992884 KiB |
| `Examples.StringStoreLite.Getters` | 332086 | 267 | 7033288 KiB |
| `Examples.UniswapV2Pair.SkimSafeTransferReturn` | 27086 | 11 | 4639084 KiB |
| `Examples.UniswapV2Pair.SkimSecondRuntime` | 39325 | 35 | 4284112 KiB |
| `Examples.UniswapV2Pair.SyncRuntime` | 112845 | 33 | 2896960 KiB |

The peak does not grow with the module's size: the largest file has the
fourth peak, and a file of 134 KB has the largest. So the charge is one
constant, 10 GiB, the largest peak rounded up. The cap margin 3/2 is the
ratio of the largest peak to the mean peak (9.83 GiB against 6.30 GiB),
because a probe of a module that still mends grows past the largest peak
seen. The reserve, 16 GiB, covers the `.olean` file pages that the probes
map (`RssFile` up to 1.8 GiB for one probe, about 13 GB summed over the live
processes of run 7, shared) and the other processes of the host. On this host
on 2026-11-06, `MemAvailable` was 34480068 KiB, so the default limit was
17702852 KiB, which admits one probe at a time beside the driver.

### The driver's own memory

The run-7 driver had a resident size of 24.7 GiB, later 30.25 GiB
(`RssAnon` 30251216 KiB). At that time its ledger held 10 replayed modules,
and 113 module files in the main checkout differed from `HEAD`. So 103
ended mends waited for the replay in `Flow.plans`: the canonical head had not
ended. Each plan kept, for every round, the syntax nodes at every open site
(`nodesAt`). A probe `node` reply on `Getters.lean` gave 9 nodes, 144 tokens
and 3460 bytes of node text per offset (mean of 20 offsets), and `diagnose`
reads two offsets for each site that a rule answers. The plan needs the
nodes only for the decision-D12 warnings. Now a round computes its warnings
where the nodes are (`followWarnings`) and keeps only them. The plans still
keep the open sites of each round, for the replay of `Mending.step`. The
driver's measured size is part of the charged total, so plans that wait for
the replay stop new admissions before they exhaust the limit.

## Decisions

C1. The shell starts one probe process for each module that it mends, and that process serves every attempt on the module.
C2. The probe imports the module's imports one time, in its elaboration of the module file, and again only when a request's import header differs from the loaded header.
C3. One probe request returns the declaration regions and the nodes at given byte offsets of one file version.
C4. The shell reads the diagnostics of an attempt from the module's one probe process, and that process keeps the elaborated state of the commands before the first changed command.
C5. The probe's diagnostics for a file text equal the diagnostics of `lake env lean --json` for the same text, in severity, range and message text.
P1. A prefetch holds at most one candidate for each theorem or lemma proof body.
P2. A prefetch attempts only a body region whose declaration kind is theorem or lemma.
P3. The Core decides only the head site, with `Mending.step`, so the commit order equals the sequential run.
P4. The shell attempts the prefetched candidates at the same time, each in its own attempt, within the worker budget.
P5. The key of a kept result is the declaration index, the edited declaration text, the statements of the earlier declarations, and the bodies of the earlier declarations that are not theorems or lemmas.
P6. A declaration with more than one open error contributes only its earliest site to a prefetch.
P7. A prefetch excludes a D12 combined candidate, because that candidate changes a statement and a later declaration can depend on it.
P8. A module starts its mend as soon as every module that it imports builds with its mended text, in its own attempt worktree, and it does not wait for a module that it does not import.
P9. Frontier modules never import each other, so their mends do not interact.
P10. The driver commits a module's accepted patches only after it commits every module before it in the canonical (module topological) order.
P11. Only the driver writes the mend branch, so the branch has one writer.
P12. The driver appends the ledger entries in the canonical sequential order, not in completion order.
P13. When a module's mend ends with no residue, the driver writes the mended file into the main checkout and builds that one module, with no commit.
P14. The shell attempts the next N head candidates of one site at the same time, each in its own worktree.
P15. The Core accepts the first candidate that passes in rule order, not the first worktree that finishes.
P16. The shell discards every speculative result after the accepted candidate in rule order.
P17. The scheduler bounds the live Lean process count by the available memory, not by the core count: one memory limit, with each work item charged its estimated peak (P24).
P18. An attempt worktree symlinks the shared dependency build and keeps its own root build directory.
P19. A wallclock site is rebuilt alone, so its verdict is the quiescent verdict.
P20. When the head candidate has a kept result with a valid key, the shell makes the module observation from that result and the current diagnostics of every other declaration, with no attempt.
P21. A blocked module builds one time, when every module that it imports builds, and its result is one `moduleBuild` observation.
P22. A module's followed-rule snapshot is the set of body rules that the modules it imports, directly or through other modules, accepted.
P23. The driver commits through the git index, so a module's file in the main checkout changes only when its mend ends.
P24. A module or a nested probe starts only when the driver's measured size plus the 10 GiB charge of each running item and of the new item, and the measured tree plus each live probe's remaining charge plus the new charge, fit the limit (`--max-memory`, else `MemAvailable` minus 16 GiB); when nothing runs, one item starts; each probe runs under `lean -M` at 15 GiB, and a probe over its cap stops the run with `CapExceeded`.
P25. The default speculative width is 4, and `--speculate 1` attempts one candidate at a time.
X1. A site position is the pair (declaration index in source order, bytes from the error to the end of that declaration).
X2. The Core sorts the open sites by that position, so the head site is the earliest error.
X3. An edit is accepted when the earliest open position moves strictly toward the end of the file.
X4. An edit is accepted only if it removes one instance of the head's failure and every failure it adds is in the attempted site's declaration, after the bytes it changed.
X5. The measure is the five-tuple (declarations after the head, head reach, open sites, head candidates, head replacement length).
X6. D10 fixes the declaration set, so an earlier declaration's position never changes under a later edit.
X7. A D12 statement follow and its body edit are one candidate, so the earliest error never moves back.
X8. The measure uses Lean core Prod.Lex only, and it is not a multiset order.

## Slices

Each slice is one testable unit of work. The slices run in dependency order. An
acceptance check runs the real program. Every slice runs the gate
(`scripts/gate.sh`). Each slice adds one fixture under `tests/` that shows the
new behavior.

A worker has at most one hour (`dispatcher.task_timeout`). One EVMLean run
takes about three hours, so no slice names an EVMLean run as its check. The
operator runs the EVMLean checks after the merges: the diagnostic equality
check after S0b, the `Semantics` 1040 check after S1b, and the tree-equality
check after S5. Each slice adds one named step to `scripts/gate.sh`, so its
check is visible in the gate's JSON output.

The branch `s1-partial` (commit `5885691`) holds the first S1 worker's
captured work. It builds, it has no `sorry`, and `lake test` reports 0 failed.
It has the coordinates, the sort, acceptance by coordinate and the five-tuple
measure, and part of the D12 combined candidate. It has no runner and no
fixture.

### S0a. One probe process per module

Implements C1, C2, C3.

Files: `probe/Probe.lean`, `LeanMend/Shell/Target.lean`,
`LeanMend/Shell/Driver.lean`, `scripts/gate.sh`.

Acceptance check:
- A runner `tests/probe-serve.sh` starts the probe `serve` command on a fixture
  module. It sends requests for three versions of the file. It asserts that
  each reply equals the output of the `regions` and `node` commands on the same
  version.
- The ledger of a run on `tests/fixtures/expose-two` holds one probe start for
  the module. The run's branch tree equals the tree of the same run with the
  lean-mend binary from before this slice.
- The runner prints the wall time of one request and the peak resident size of
  the probe process.
- `scripts/gate.sh` runs `tests/probe-serve.sh` as the step `one probe process
  per module`, and the gate's JSON reports every step passed.

### S0b. Reuse of the elaborated commands before an edit

Implements C4, C5. Depends on S0a.

Files: `probe/Probe.lean`, `LeanMend/Shell/Target.lean`,
`tests/server-diag.sh`, `tests/fixtures/server-diag`, `scripts/gate.sh`.

Acceptance check:
- A runner `tests/server-diag.sh` opens a fixture module in one probe `serve`
  process and sends at least five changes: an edit that removes an error, an
  edit that adds an error, an edit in the first declaration, an edit in the
  last declaration, and a revert. After each change, it asserts that the
  probe's messages equal the messages of `lake env lean --json` on the same
  text: the same JSON objects (severity, range, message text, kind), in the
  same order.
- The same runner generates a module of 200 theorems and edits a theorem near
  its end. It asserts the same equality, and it asserts that the change takes
  less than a quarter of the full-file `lake env lean --json` time.
- The runner prints the wall time of each change, the full-file time and the
  peak resident size of each probe process.
- The branch trees of the runs in `tests/expose.sh`, `tests/follow-pair.sh`,
  `tests/speculate.sh` and `tests/rename.sh` equal the trees of the same runs
  with the lean-mend binary from before this slice.
- `scripts/gate.sh` runs `tests/server-diag.sh` as the step `diagnostics from
  the Lean server`, and the gate's JSON reports every step passed.

The operator then checks C5 on EVMLean. For each commit of run 21's mend
branch, the probe's diagnostics of the changed module equal the diagnostics of
`lake env lean --json`.

### S1a. Declaration coordinates and the sorted site list

Implements X1, X2, X6.

Files: `LeanMend/Spec/Types.lean`, `LeanMend/Core/Mend.lean`,
`LeanMend/Shell/Target.lean`, the probe `regions` command if it lacks the
declaration index.

Acceptance check:
- A new fixture `tests/fixtures/order-first`: one module where Lean reports a
  later error before an earlier one. A runner `tests/order.sh` runs lean-mend
  on it and asserts that the first attempt in the ledger is at the
  source-earliest site.
- `scripts/gate.sh` runs `tests/order.sh` as the step `site order by
  declaration coordinates`, and the gate's JSON reports every step passed.

### S1b. Acceptance of any number of later errors, and the five-tuple measure

Implements X3, X4, X5, X8. Depends on S1a.

Files: `LeanMend/Core/Mend.lean`, `LeanMend/Spec/Types.lean`,
`LeanMend/Spec/Termination.lean`, `LeanMend/Spec/Invariant.lean`,
`LeanMend/Shell/Driver.lean`.

Acceptance check:
- A new fixture `tests/fixtures/expose-two`: one edit fixes the head error and
  exposes two later errors in the same declaration. A runner `tests/expose.sh`
  asserts that the Core accepts the edit.
- A new fixture `tests/fixtures/expose-back`: one edit fixes the head error and
  leaves an error earlier than the old head. The same runner asserts that the
  Core rejects the edit.
- `Mending.step_measure` states the five-tuple decrease, and no LeanMend
  constant depends on `sorryAx`.
- `scripts/gate.sh` runs `tests/expose.sh` as the step `exposure of later
  errors`, and the gate's JSON reports every step passed.

### S1c. The D12 combined candidate

Implements X7. Depends on S1b.

Files: `LeanMend/Core/Ops.lean`, `LeanMend/Core/Propose.lean`,
`LeanMend/Shell/Target.lean`.

Acceptance check:
- A new fixture `tests/fixtures/follow-pair`: a `valCompare` body edit whose
  statement follow is needed. A runner `tests/follow-pair.sh` runs lean-mend
  with `--follow-definition-changes` and asserts that the ledger holds one
  attempt with both edits, and that the Core accepts it.
- `tests/follow.sh` still passes.
- `scripts/gate.sh` runs `tests/follow-pair.sh` as the step `D12 body edit and
  statement follow as one candidate`, and the gate's JSON reports every step
  passed.

### S2a. The prefetch selection in the Core

Implements P1, P2, P6, P7. Depends on S1c.

Files: `LeanMend/Core/Mend.lean`, `tests/OpsTest.lean`.

The branch `worker/lea-fc0` (commit `6f9984c`) has `Mending.batch`,
`batch_distinct` and `batch_bodyOnly`. It also has `Mending.stepBatch` and a
`stepBatch_measure` that is false and has a `sorry`. This slice keeps the
selection and its two proofs. It does not add `stepBatch`.

Acceptance check:
- `Mending.batch_distinct` and `Mending.batch_bodyOnly` exist with the
  statements in the table above, and no LeanMend constant depends on
  `sorryAx`.
- `tests/OpsTest.lean` shows `Mending.batch` on a module state with three
  failing theorem bodies, one failing `def` body, a second open site in one of
  the theorems, and one D12 combined candidate. The batch holds the earliest
  site of each theorem that has no D12 candidate. It holds no `def` site.
- The gate's JSON reports every step passed.

### S2b. Prefetched attempts in the Shell

Implements P3, P4, P5, P20. Depends on S2a, S0b.

Files: `LeanMend/Shell/Driver.lean`, `LeanMend/Shell/Target.lean`,
`scripts/gate.sh`.

Acceptance check:
- A new fixture `tests/fixtures/batch`: one module with several theorem bodies
  broken by one rule, and one theorem whose first candidate fails. A runner
  `tests/batch.sh` asserts three facts. The ledger records a prefetched attempt
  for each theorem site. Each accepted site uses its kept result with no second
  attempt. The branch tree equals the tree of a `--prefetch 0` run on the same
  fixture.
- A second fixture has a `def` before a theorem site, and a candidate that
  changes the body of that `def`. The runner asserts that the shell does not
  use the theorem's kept result after that change. It also asserts that the
  branch tree equals the tree of a `--prefetch 0` run.
- `scripts/gate.sh` runs `tests/batch.sh` as the step `prefetched attempts
  across theorem bodies`, and the gate's JSON reports every step passed.

### S3a. The fleet of Mending states in the Core

Implements P9. Depends on S1c.

Files: `LeanMend/Core/Run.lean`, `LeanMend/Spec/Termination.lean`,
`tests/OpsTest.lean`.

Acceptance check:
- `frontier_pairwise_indep`, `openCount_finishAll` and `Fleet.step_wf` exist,
  `openCount_settled` still holds, and no LeanMend constant depends on
  `sorryAx`.
- `tests/OpsTest.lean` shows a fleet of two `Mending` states that receive
  observations in either order and reach the same final state.
- The gate's JSON reports every step passed.

### S3b. Parallel frontier modules in the Shell

Implements P10, P11, P12. Depends on S3a.

Files: `LeanMend/Shell/Driver.lean`, `LeanMend/Shell/Target.lean`,
`scripts/gate.sh`.

Acceptance check:
- A new fixture `tests/fixtures/fleet`: two independent frontier modules, each
  with one break. A runner `tests/fleet.sh` asserts that the attempts of the
  two modules overlap in time, that no two modules share a worktree, that the
  driver commits them in the canonical order, and that the ledger replays
  them in that order.
- `scripts/gate.sh` runs `tests/fleet.sh` as the step `parallel frontier
  modules`, and the gate's JSON reports every step passed.

### S3c. Dataflow scheduling across modules

Implements P8, P10, P13, P21, P22, P23. Depends on S3b. Replaces the wave
loop of S3b: a module starts when its imports build, not when a wave ends.

Files: `LeanMend/Core/Run.lean`, `LeanMend/Core/Graph.lean`,
`LeanMend/Spec/Termination.lean`, `LeanMend/Shell/Driver.lean`,
`tests/OpsTest.lean`, `scripts/gate.sh`.

Acceptance check:
- `ready_imports_built`, `frontier_sub_ready`, `RunState.moduleBuilt_settled`
  and `blockedCount_moduleBuilt` exist with the statements in the Level 2
  table, and no LeanMend constant depends on `sorryAx`.
- A new fixture `tests/fixtures/dataflow`: `Slow` and `Fast` are independent,
  and `Dep` imports `Fast` only. Each accepted fix of `Slow` waits, in a test
  barrier, until `Dep`'s first attempt starts. `Clean`
  imports `Fast` and has no break. A runner `tests/dataflow.sh` asserts from
  the ledger that `Dep`'s first attempt starts before `Slow`'s mend ends, that
  the commits on `lean-mend/mend` and the `diagnosed` lines follow the
  canonical order, that `Clean` gets one `moduleBuild` with status `built`,
  and that the branch tree equals the expected tree. The expected tree is
  `main`'s tree with each broken file replaced by a hand-written file in
  `tests/fixtures/dataflow/expected`.
- `tests/fleet.sh` and every other runner still pass.
- `scripts/gate.sh` runs `tests/dataflow.sh` as the step `dataflow scheduling
  across modules`, and the gate's JSON reports every step passed.

### S4. Speculation across the candidates of one site

Implements P14, P15, P16. Depends on S1c.

Files: `LeanMend/Core/Mend.lean`, `LeanMend/Shell/Driver.lean`,
`LeanMend/Shell/Target.lean`.

Acceptance check:
- A new fixture `tests/fixtures/speculate`: one site whose accepted candidate
  is the third in rule order. A runner `tests/speculate.sh` asserts the ledger
  records the speculative attempts, and the branch commits the third candidate.
- The committed candidate equals the candidate of a sequential run of the same
  fixture.
- `scripts/gate.sh` runs `tests/speculate.sh` as the step `speculation across
  candidates`, and the gate's JSON reports every step passed.

### S5. The memory limit

Implements P17, P24. Depends on S3c, S4.

Files: `LeanMend/Core/Sched.lean`, `LeanMend/Shell/Memory.lean`,
`LeanMend/Shell/Driver.lean`, `LeanMend/Shell/Target.lean`,
`LeanMend/Shell/Parse.lean`, `probe/Probe.lean`, `tests/probe-bound.sh`,
`tests/fixtures/probe-bound`, `tests/cap-stop.sh`, `tests/fixtures/cap-stop`,
`scripts/gate.sh`.

Acceptance check:
- `tests/fixtures/probe-bound`: four independent modules, each with one
  break and two candidates. `tests/probe-bound.sh` runs it with
  `--max-memory 21` and asserts from the `probeStart` and `probeStop` lines
  that at most 2 probes are live at any time, and that every admission fits
  the limit or ran when nothing ran. A run with `--max-memory 64` has more
  than 2 live probes. A run with `--max-memory 1 --speculate 3` finishes. A
  run with no flag records `MemAvailable` minus 16 GiB. Each run's branch
  tree equals the hand-written expected tree, and each run commits in the
  canonical order. A run with `--probe-cap 1200` stops with `CapExceeded`.
- `tests/fixtures/cap-stop`: two modules whose probes give no reply and do
  not exit. One of them writes the cap text. `tests/cap-stop.sh` asserts
  that the run exits 3 with `capExceeded` for that module within 60 s of
  the text, and that no probe of the run is left.
- `scripts/gate.sh` runs `tests/probe-bound.sh` as the step `memory bound on
  live probe processes` and `tests/cap-stop.sh` as the step `a probe that
  writes the cap text and does not exit stops the run with capExceeded`, and
  the gate's JSON reports every step passed.

P18 and P19 are not part of this slice.

The operator then runs the end-to-end check: a sequential and a parallel
EVMLean v4.29.0 → v4.33.1 run of the same target produce the same mend-branch
tree (`git rev-parse lean-mend/mend^{tree}`), and the parallel run takes less
wall time. The report states both times.

## Risks

- **Memory per Lean process.** One probe of EquiVM run 7 reached 9.83 GiB.
  Swap is 0, so an overcommit triggers the OOM killer, not a slowdown. The
  run caps its work by one memory limit (P17, P24, § The memory limit). The
  module builds are charged but not capped: `lake build` starts their `lean`
  processes, and the driver gives them no `-M`. The certificate probes run
  before and after the schedule, at most 4 and at most as many charges as
  the limit holds (`certificateJobs`). The driver's own plans count in the
  charged total; a plan keeps its rounds' open sites until its replay.

- **Disk per attempt worktree.** The dependency build is 2.9 GiB. The root
  build is 38 MiB. A worktree symlinks the dependency build read-only and keeps
  its own root build (P18). So the marginal disk per worktree is about 38 MiB,
  not 3.0 GiB. A plain copy of the whole `.lake` would cost 3.0 GiB per
  worktree and must not be used. This host has no reflink (zfs 2.2.2 block
  clone is off), so `cp --reflink` is not available. A hardlink copy
  (`cp -al`, 3.89 s, 0 extra blocks) is an option only if Lake writes each
  output by a temporary file and a rename. The slice must verify that write
  pattern before it relies on hardlinks.

- **Git index locks on a shared repo.** Git takes `index.lock` for each commit
  and each worktree operation. Parallel writers to one index collide. The
  design avoids the collision: only the driver writes the mend branch (P11),
  and it commits one patch at a time. Each attempt worktree is a separate git
  worktree with its own index, so the worktrees do not share the lock. The
  driver must serialize `git worktree add` and `git worktree remove`, because
  those commands write the shared `.git/worktrees` directory.

- **Host contention raises wallclock timeouts.** More parallel builds raise the
  chance of a `wallclock` timeout. The design rebuilds a wallclock site alone
  (P19). A second timeout halts the run with `HostTimeout`. So contention can
  halt a run that the sequential run finishes. The scheduler lowers the risk by
  the memory and core caps (P17).

- **The determinism of trees against commit SHAs.** The acceptance check
  compares branch trees, not commit SHAs. A commit SHA also depends on the
  committer date. A byte-for-byte branch needs a fixed `GIT_COMMITTER_DATE` and
  `GIT_AUTHOR_DATE`. The slice must set both, or the check compares trees only.

- **Memory of long-lived processes.** A probe process keeps the imported
  environment and the elaborated state of every command of its module, with
  the info trees (`internal.cmdlineSnapshots` is off, C4). On EquiVM run 7 a
  probe reached 9.83 GiB (§ The memory limit). The charge and the cap of P24
  come from those peaks.
