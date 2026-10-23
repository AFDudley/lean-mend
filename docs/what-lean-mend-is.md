# What lean-mend is

## The problem

Lean releases a new minor version about once a month. Mathlib and Batteries
move with it. A project that pins a toolchain falls one version further behind
each month. When the project moves, its build breaks.

Most of the breaks are mechanical. A small number of patterns recur at many
sites. Today people and agents repair them by hand, one site at a time.

## The evidence

**EquiVM, Lean v4.29.0 to v4.33.1 (2026-10-22).** Four agents worked on the
port for about 10.5 hours. They made 211 hand edits. They found the scope one
layer at a time: each repair of an upstream module unblocked downstream
modules, which then failed. The work stopped before the build was green. The
report is `EquiVM/.scratch/lean-v4.33.1-report.md` on the `AFDudley/EquiVM`
branch `lean-v4.33.1`.

The error classes were few and patterned:

- A library rename: Batteries `RBMap` and `RBSet` became `RBTree.RBMap` and
  `RBTree.RBSet` (44 references in 11 files).
- `match` on a literal pattern over a wrapped number (`match p with | 1`) needs
  a decidability instance that the new match compiler does not synthesize.
- `Fin` coercions: a value and its coercion no longer match syntactically.
- Five literal forms that were definitionally equal and now need a proof step,
  for example `UInt256.ofNat N` against `{ val := N }`.
- `simp` set changes, for example `Id.run` no longer unfolds by default.

**The Goedel workbook, Lean v4.8 to v4.27 (`mike1729/goedel-workbook-lean427`).**
Python scripts migrated 29,750 proofs. A rename table fixed 18.4 % of the
files. One error class (a `field_simp` change) was 67 % of all errors, and one
scripted rewrite fixed about 90 % of that class. 94.1 % of the proofs
compiled at the end.

The lesson from both: compile everything, sort the errors into classes, repair
each class with a rule, and leave only the residue to a person or an agent.

## What lean-mend does

1. It records a **baseline certificate** of the target at the old toolchain:
   the modules that build, and for each theorem its statement and its axioms.
2. It moves the target to the new toolchain, or it accepts a target that
   another tool moved (`lean-update`, `lean-bump`).
3. It builds the target in module-dependency order and reads each failure as
   structured diagnostics.
4. It sorts each failure into an **error class** and finds the **rules** for
   that class.
5. It tries each rule's **candidates** at the failing **site**, in order. It
   rebuilds only the affected module. It keeps the first candidate that builds
   and passes the invariant check. It reverts the others.
6. It repeats until the build is green or only **residue** remains.
7. It hands each residue site to an agent or a person, with the class, the
   failed candidates and the goal state. A repair that succeeds becomes a
   **proposed rule**.
8. It writes an **after certificate** and proves that it equals the baseline.

## Scope

In scope:

- Lean 4 projects built by Lake, with or without Mathlib.
- Breaks caused by changes in Lean, Lake, Batteries, Mathlib or another Lake
  dependency.
- Repairs inside proofs, imports, `open` lines and identifier references.
- Repairs inside definition bodies, flagged for a semantic check (see
  [verification.md](verification.md)).

Out of scope:

- Moving the pins. `lean-update` and `lean-bump` already do that.
- General proof search. lean-mend applies known repairs. It hands new problems
  to an agent; it does not search for proofs itself.
- Changing any theorem statement. lean-mend never edits a statement, except to
  replace a deprecated name with its alias target (see
  [verification.md](verification.md)).

## Acceptance test

lean-mend is done for its first version when this test passes:

> On `AFDudley/EquiVM` at upstream `fc74a646` (Lean v4.29.0), lean-mend moves
> the project to Lean v4.33.1 and stops with every baseline module building,
> or with a residue list. The after certificate shows the same 294 certificate
> theorems with the same axiom sets as the v4.29.0 baseline. The residue list
> is smaller than 211 sites. Every repair is recorded in the ledger with its
> rule.

The baseline evidence for this test already exists in
`EquiVM/.scratch/baseline/`.
