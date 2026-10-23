# Process

lean-mend follows the strata of `exophial4/docs/process.md`. Each stratum is a
layer whose parts are the primitives of the next. A stratum is done when its
gate is green, never when a reader agrees. A red gate is the deliverable: no
ratchet, no baseline file, no `xfail`, no skip.

## Stage 0

The first complete machine is written by hand (concept D10). It runs end to
end on one fixture before any second rule or second class exists. It then
mends itself where it can: a lean-mend toolchain bump is a lean-mend run on
the lean-mend source.

## The strata

| Stratum | Work in lean-mend | Gate |
|---|---|---|
| 0. Vocabulary | [glossary.md](glossary.md); every term in a type name is in the glossary | static: every `structure` and `inductive` name in `Spec/` and `Core/` appears in the glossary |
| 1. State space as a type | `Spec/Types.lean`: one type per state, operands with their evidence fields | `lake build` |
| 2. Invariant first | `Spec/Invariant.lean`, before `Spec/Machine.lean` has a transition | static: `Invariant.lean` has no import of `Machine.lean` |
| 3. Parse at the edge | `Shell/Parse.lean`: JSON to typed operands; `Core` takes no `Json` | static: no `Lean.Json` in `Core/` or `Spec/` |
| 4. The flat chart | level 1 of [machine.md](machine.md); `Mending` is the only composite state | review of the chart against the transition table; the table is data in `Spec/Machine.lean` |
| 5. Totality | every `match` over `ErrorClass`, `State` and `Refusal` is exhaustive | mutation: add a constructor to `ErrorClass` in a scratch copy and assert that `lake build` fails in `Classify.lean` for that reason |
| 6. Shallow run | the driver runs one fixture from `Idle` to `Done` | execution: `lake test` on the first fixture |
| Tour | the fixtures, ordered so every transition fires | execution: the ledger of the fixture run names every transition |
| 8. Properties | Plausible properties on `Core`; the theorems in `Spec` | `lake build` with no `sorry`; `lake test` runs the properties |
| Next chart | level 2: sites and candidates inside `Mending`, with its gluing invariant | the strata again, inside `Mending` |

## Order of work

Done: step 1; step 2; in step 3, the `baseline` transition against a real
target (`lean-mend baseline`, `tests/baseline.sh`).

1. Strata 0 to 2 for level 1. These documents are the start of stratum 0.
2. The probe, compiled and run under v4.29.0, v4.33.1 and v4.35.0. Without the
   probe there is no certificate and no site.
3. Strata 3 to 6 for level 1, with one fixture: an `unknownIdentifier` break
   that the alias map repairs.
4. Level 2, with the fixtures for each class in [rules.md](rules.md).
5. The EquiVM acceptance test.
6. Residue packets and the fixed runner for proposed rules.
7. Attribution by bisect.
8. The scheduled workflow.

## Repository gates

`scripts/gate.sh` is the commit gate. `.exophial/config.yaml` names it as
`gate.command`, and exophial runs it in the branch worktree before each
merge. It runs, in order:

1. the boundary check: no `Spec` or `Core` module imports a `Shell` module;
2. `lake build`;
3. `tests/NoSorry.lean`: no `LeanMend` constant depends on `sorryAx`;
4. `lake test`: the tour;
5. `tests/probe-matrix.sh`: the probe under every supported toolchain.

The vocabulary check (stratum 0) is not in the gate yet.
