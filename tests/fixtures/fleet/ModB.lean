/-! Paired with `ModA.lean` for `tests/fleet.sh`: an independent module with
its own break. `ModA` and `ModB` do not import each other, so both mend at
the same time. `ModB`'s fix makes the kernel decide a count half the size of
`ModA`'s. So its attempt lasts seconds and overlaps `ModA`'s attempt, and it
still ends first. An attempt reads its diagnostics from the module's probe
process (`docs/parallel.md` C4), so a fix with no slow step ends in about
1 ms, before the other module's attempt starts. -/
set_option maxRecDepth 1000000

/-- The same plain recursive count as `ModA.slowCountA`. -/
def slowCountB : Nat → Nat
  | 0 => 0
  | n + 1 => slowCountB n + 1
theorem fooB : True := by
  exact unknownHeadB
