# Process

lean-mend follows the strata of `exophial4/docs/process.md`. Each stratum is a
layer whose parts are the primitives of the next. A stratum is done when each
of its gates passes, never when a reader agrees. A gate that fails is the
deliverable: no ratchet, no baseline file, no `xfail`, no skip. A gate is one
check that runs; a decision that a person or an agent makes is a judgment, not
a gate ([glossary.md](../glossary.md)).

## Stage 0

The first complete machine is written by hand (concept D10). It runs end to
end on one fixture before any second rule or second class exists. It then
mends itself where it can: a lean-mend toolchain bump is a lean-mend run on
the lean-mend source.

## The strata

| Stratum | Work in lean-mend | Gates and judgments |
|---|---|---|
| 0. Vocabulary | [glossary.md](../glossary.md); every term in a type name is in the glossary | static: every `structure` and `inductive` name in `Spec/` and `Core/` appears in the glossary |
| 1. State space as a type | `Spec/Types.lean`: one type per state, operands with their evidence fields | `lake build` |
| 2. Invariant first | `Spec/Invariant.lean`, before `Spec/Machine.lean` has a transition | static: `Invariant.lean` has no import of `Machine.lean` |
| 3. Parse at the edge | `Shell/Parse.lean`: JSON to typed operands; `Core` takes no `Json` | static: no `Lean.Json` in `Core/` or `Spec/` |
| 4. The flat chart | level 1 of [machine.md](machine.md); `Mending` is the only composite state | judgment: a review of the chart against the transition table; the table is data in `Spec/Machine.lean` |
| 5. Totality | every `match` over `ErrorClass`, `State` and `Refusal` is exhaustive | mutation: add a constructor to `ErrorClass` in a scratch copy and assert that `lake build` fails in `Classify.lean` for that reason |
| 6. Shallow run | the driver runs one fixture from `Idle` to `Done` | execution: `lake test` on the first fixture |
| Tour | the fixtures, ordered so every transition fires | execution: the ledger of the fixture run names every transition |
| 8. Properties | Plausible properties on `Core`; the theorems in `Spec` | `lake build` with no `sorry`; `lake test` runs the properties |
| Next chart | level 2: sites and candidates inside `Mending`, with its gluing invariant | the strata again, inside `Mending` |

## Laws

[laws.md](laws.md) is the one registry of lean-mend's laws, the invariants it
must never violate. This follows exophial (`exophial/docs/merge_plan.md` §
Stage MLAW, and its registry `src/exophial/core/contract.py`).

**A law change has four parts, in one change:** the law's statement in
laws.md, the gate that checks it, a fixture that is red before the fix, and the
code fix that makes that gate pass. A law has no counted exception.

**A defect that a law covers is a datapoint, not its own work item.** Record
it in the law's table in laws.md, with its date and state. The work item is to
move the law up one rung, so that the class of defect cannot occur again. A
defect that no law covers gets its own work item. If the defect shows a new
class, add the law first.

**A work item is small.** One law rung, or one function with its test. Its
acceptance is a named runner or test that passes in the container that runs `gate.command`.
An acceptance check on EquiVM data runs on the host, after the merge.

## Order of work

Done:

1. Strata 0 to 2 for level 1.
2. The probe, under v4.29.0, v4.33.1 and v4.35.0.
3. Strata 3 to 6 for level 1 (`tests/rename.sh`).
4. Level 2, with the fixtures for each class in [rules.md](rules.md).
5. The EquiVM acceptance test (runs 1 to 10).
6. Residue packets and the runner for proposed rules.
7. Level 3, the axiom repair ([machine.md](machine.md) § Level 3).
8. Static-diff slices 1 to 3 and 5 ([static-diff.md](static-diff.md)).

Open:

9. The open datapoints of [laws.md](laws.md), one law rung at a time.
10. Static-diff slices 4, 6 and 7.
11. Attribution by bisect.
12. The scheduled workflow.

## The repository's gates

`scripts/gate.sh` is the command (`gate.command`) that runs the gates at the
commit boundary. Each step is one gate. It runs, in order:

1. the boundary check: no `Spec` or `Core` module imports a `Shell` module;
2. `lake build`;
3. `tests/NoSorry.lean`: no `LeanMend` constant depends on `sorryAx`;
4. `lake test`: the tour and the unit tests;
5. `tests/probe-matrix.sh`: the probe under every supported toolchain;
6. every runner under `tests/` that runs lean-mend on a real fixture. The
   script lists them; each step names its runner.

In armada-laconic-mono (formerly evm-proof-toolchain), `scripts/lean-mend-gate.sh`
runs `scripts/gate.sh` as one step of the monorepo's `scripts/gate.sh`. It
stores the verdict under a key that covers every file
of `lean-mend/` and the installed toolchains (law LM3), so a commit that does
not change `lean-mend/` reads the stored verdict.

`scripts/gate.sh` stops at the first failed step and exits 1. Each step's output goes
to stderr. stdout carries one JSON object and nothing else: one key
`"steps.<step name>.ok"` per step that ran, then `"passed": N` and
`"failed": 0 or 1`. A failed step is the last step key, with value `false`. An exophial spec observes
this object (`stdout_json`); an exit code alone is a vacuous check.

### Check scripts

Every check script prints one JSON object on stdout and nothing else; its other output goes to stderr.

A runner under `tests/` sources `tests/lib/report.sh`, records each check
with `pass NAME` or `failed NAME`, and ends with `report`. Its object is
`{"runner": …, "checks.<check name>.ok": true|false, …, "passed": N, "failed": N}`.
The keys are flat on purpose: exophial reads a whole `stdout_json` field path
as a top-level key first, so a spec can address one step or check by name,
and a name that holds a dot (`Dep.new`, `v4.33.1`) still resolves. A nested
object would split such a name at its dots.
A runner that measures a number records it with `measure NAME N`, as the key
`"measures.<NAME>": N`. A measure is not a check, and it does not change
`passed` or `failed`.
A runner builds what it runs. A runner that runs lean-mend sources
`tests/lib/lean-mend.sh`, which builds the binary and sets `$bin`. exophial
runs each check script alone in the container that runs `gate.command`, so a runner cannot
depend on an earlier step of `scripts/gate.sh`.
`tests/NoSorry.lean` prints `{"runner": "NoSorry", "checked": N,
"sorry_dependents": [names]}`. A runner that stops early prints nothing on
stdout, so a check over its JSON fails. An exophial spec observes these objects
(`stdout_json`); an exit code alone is a vacuous check, and exophial's SPECIFY
gate refuses it.

The vocabulary check (stratum 0) is not a step of `scripts/gate.sh` yet.
