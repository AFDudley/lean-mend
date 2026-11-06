/-! `tests/dataflow.sh` (`docs/parallel.md` § Level 2, P8, P13): `Slow`
does not import `Fast`, and `Dep` imports `Fast` only. Each accepted fix of
`Slow` makes the kernel decide a plain recursive count, so each of its two
attempts takes several seconds. `Dep` must start its mend as soon as `Fast`
is mended and built, before `Slow`'s mend ends. -/
set_option maxRecDepth 1000000

/-- A plain recursive count, not one of Lean's accelerated `Nat` operations
(the device of `tests/fixtures/speculate/App.lean`). Deciding
`slowCount n = n` for a large `n` takes the kernel several seconds. -/
def slowCount : Nat → Nat
  | 0 => 0
  | n + 1 => slowCount n + 1

theorem fooS1 : True := by
  have _slow1 : slowCount 200000 = 200000 := by decide
  trivial

theorem fooS2 : True := by
  have _slow2 : slowCount 199999 = 199999 := by decide
  trivial
