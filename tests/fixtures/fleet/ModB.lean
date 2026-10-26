/-! Paired with `ModA.lean` for `tests/fleet.sh`: an independent module with
its own break, fixed by a fast candidate. `ModA` and `ModB` do not import
each other, so both are frontier modules at the same time. -/
theorem fooB : True := by
  exact unknownHeadB
