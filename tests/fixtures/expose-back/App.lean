/-! S1b (`docs/parallel.md` X4): `tests/expose.sh` breaks this module, then
runs lean-mend with the rule in `rules/`. The rule replaces the head error
with text that fails itself: `exact unknownA` and `exact unknownB` are errors
inside the edit's own bytes, not errors the edit exposed. The Core rejects the
edit (`Candidate.leavesOnlyLater`). -/
theorem foo : True ∧ True := by
  exact unknownHead
