/-! S1b (`docs/parallel.md` X4): `tests/expose.sh` breaks this module, then
runs lean-mend with the rule in `rules/`. The rule replaces the head error
with text that leaves its own, still-open errors at a byte reach larger than
the old head's: a position earlier in the declaration than the old head. The
Core rejects the edit. -/
theorem foo : True ∧ True := by
  exact unknownHead
