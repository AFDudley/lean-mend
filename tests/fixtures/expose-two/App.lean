/-! S1b (`docs/parallel.md` X3, X4): `tests/expose.sh` breaks this module,
then runs lean-mend with the rule in `rules/`. Before the edit Lean reports
`exact unknownHead` and, after the failed tactic, "No goals to be solved" at
the first bullet: the two bullet errors stay hidden. The rule replaces
`exact unknownHead` with `constructor`. Lean then checks the bullets and
reports `unknownA` and `unknownB`: two errors that were already in the text,
after the edited bytes, in the same declaration. The Core accepts the edit. -/
theorem foo : True ∧ True := by
  exact unknownHead
  · exact unknownA
  · exact unknownB
