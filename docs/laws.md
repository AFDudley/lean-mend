# Laws

This file is the one registry of lean-mend's laws. A law is an invariant that
lean-mend must never violate. Other documents state the design that makes a law
hold. They point here; they do not state a law again.

[process.md](process.md) § Laws gives the form of a law change and the rule for
a defect that a law covers.

## Rungs

Each law has a current rung and a target rung, on this ladder (from strongest):

1. **Construction.** No value of the type can violate the law.
2. **Proof.** A theorem in `LeanMend/Spec/`, checked by `lake build`.
3. **Gate.** A check in `scripts/gate.sh` that fails when the law fails.
4. **Review.** A reader checks it. This is not enforcement.

A law that is at rung 4 has an open pebble that moves it up.

## The laws

### LM1. No harm to the target

**Statement.** For every declaration of the baseline certificate whose module
builds after the bump: its statement is unchanged up to the alias map; its axiom
set is unchanged, or a recorded judgment accepts the difference; a changed
`def`, `instance` or `abbrev` body is accepted by a recorded judgment. Every
commit on the mend branch is an accepted patch in the ledger.

**Rung.** Statement: construction (`EditTarget` has no statement region).
Axioms and bodies: proof (`compare_nil`, `NoHarm` in `Spec/Invariant.lean`).
Mend branch: construction and proof (`Accepted`, `branchSound`).
Target: unchanged.

**Design.** [machine.md](machine.md) § The invariant.

### LM2. Termination

**Statement.** Every run stops.

**Rung.** Proof: `Mending.step_measure`, `FindingMending.step_measure`, the
`openCount_*` theorems (`Spec/Termination.lean`). Target: unchanged.

**Design.** [machine.md](machine.md) § Termination.

### LM3. Input closure

**Statement.** Every result lean-mend computes or stores (a probe output, a
certificate, a stored dependency diff, a gate verdict) is a function of its
declared inputs. A stored result is read again only under a key that covers
every input. A build that lean-mend reads was made from the source that its
trace names.

**Rung.** Gate, for the datapoints that are fixed. Target: construction (a
stored result type that carries its full input key).

**Datapoints.**

| Date | Datapoint | State |
|---|---|---|
| 2026-11-10 | `include_str` probe source not tracked by Lake: a build ran an old probe | fixed, `tests/probe-source-tracked.sh` |
| 2026-11-10 | One probe build directory for all probe sources: concurrent runs overwrote it | fixed, `tests/probe-stamp-race.sh` |
| 2026-11-10 | Dependency-diff key had no module list: a new import read a stale diff | fixed, `tests/dep-diff.sh` |
| 2026-11-11 | Dependency-diff key has no `.olean` content: a rebuilt tree read a stale diff | fixed, `tests/dep-diff-rebuild.sh` (`builtContentHash` in the key) |
| 2026-11-11 | A measurement tree's `Reasoning/Dispatch.olean` came from an edit in place; Lake accepted it as current | open |

### LM4. Coverage

**Statement.** Every analysis (certificate, dependency diff, propagation,
generated auxiliaries, computational equality) covers every declaration that
the certificate selects. No person chooses the scope.

**Rung.** Gate, for the fixed datapoint. Target: proof (each analysis takes the
certificate's selection as its input type).

**Datapoints.**

| Date | Datapoint | State |
|---|---|---|
| 2026-11-10 | `dep-diff --roots` missed `Rng.bigNat` (E2) | fixed, `tests/dep-diff-clash.sh` |
| 2026-11-11 | `gen-aux` on EquiVM did not report `Stele.Interp.allocationSizes` (E3) | not a defect: E3 is a source edit (`partial def` to structural recursion), not a toolchain change; [static-diff.md](static-diff.md) § 3 |

### LM5. No silent omission

**Statement.** A step that cannot compute a result for an item stops and names
the item. No timeout, catch or skip replaces a result.

**Rung.** Gate: `tests/CatchRethrow.lean` fails on a `catch` branch in
`LeanMend/`, `probe/` or `Main.lean` that has no `throw`. A branch that matches
on the error and rethrows the other cases passes. Target: unchanged.

**Datapoints.**

| Date | Datapoint | State |
|---|---|---|
| 2026-11-10 | `export` wrote `{"timeout": true}` for a body it could not erase | fixed (catch removed) |
| 2026-11-12 | 11 `catch` branches had no `throw` (first run of the gate): `isProof` errors counted as "not a proof" (3, probe); any `moduleNameOfFileName` error gave `_stdin`; a stamp read error gave an empty stamp (2); any `createDir` error counted as "lock held"; 4 rethrows hidden inside `stopSchedule` or an `Except` value | fixed, `tests/CatchRethrow.lean` |

### LM6. Proof irrelevance

**Statement.** lean-mend never compares the body of a theorem or of a proof
auxiliary. For those it compares the axiom set only.

**Rung.** Gate (`tests/dep-diff.sh`, `tests/GenAuxTest.lean`). Target:
construction (a row type whose theorem variant has no body field).

**Datapoints.**

| Date | Datapoint | State |
|---|---|---|
| 2026-11-10 | `DepConst` had no `kind`: theorem proof changes became body findings | fixed |
| 2026-11-10 | § 3 compared `_proof_N` auxiliaries | fixed |

### LM7. Prediction equals observation

**Statement.** The findings that the static diff predicts before a run equal the
findings that `compare` observes at its end. A difference is itself a finding
(decision S5).

**Rung.** Review. Target: gate (static-diff slice 7).

**Datapoints.**

| Date | Datapoint | State |
|---|---|---|
| 2026-11-11 | Propagation predicted E2 without `propext` | fixed, `tests/propagate.sh` (`appUsesWrapper`) |
| 2026-11-11 | `gen-aux` on EquiVM gave 228 predictions, each another declaration's auxiliary; run 10 has 0 generator-caused findings | fixed, `tests/GenAuxTest.lean` ("another declaration's equation lemma"); 0 predictions on EquiVM |

### LM8. A card follows a failed attempt

**Statement.** A finding becomes a card only after a recorded attempt to certify
or repair it failed. The card names each attempt and its reason (decision S6).

**Rung.** Gate for the attempts that exist (`tests/level3-*.sh`,
`tests/proof-only-accept.sh`, `tests/compeq.sh`). Target: construction (`Card`
requires a non-empty list of failed attempts).

**Design.** [static-diff.md](static-diff.md) § 6.

### LM9. The gate runs where the branch is judged

**Statement.** Every gate step passes in the gate image, the place where the
integrator judges a branch. A step uses only the tools that the image installs.

**Rung.** Gate: since evm-proof-toolchain `fb2e7fb9`, the monorepo gate runs
lean-mend's gate in the image (`scripts/lean-mend-gate.sh`). Target:
unchanged.

**Datapoints.**

| Date | Datapoint | State |
|---|---|---|
| 2026-11-11 | The image's `lake` wrapper set up a fixture's own git worktree as a monorepo checkout | fixed, `scripts/lake-wrapper.sh` |
| 2026-11-11 | `tests/cap-stop.sh` used `bc`, which the image lacks | fixed (jq) |
| 2026-11-11 | `tests/probe-source-tracked.sh` and `tests/probe-stamp-race.sh` used `rsync`, which the image lacks | fixed (tar) |
