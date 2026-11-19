/-! `tests/probe-bound.sh` (`docs/parallel.md` P24): one of four independent
modules, each with one break. The first candidate of the rule keeps the break,
so the Core rejects it. The second candidate fixes the break and adds a slow
decided count. So each module holds its probe for two attempts, and the four
mends overlap when the memory limit admits them.

`ModD` takes no part in the test barrier of `ModA`, `ModB` and `ModC`. -/
set_option maxRecDepth 1000000

/-- A plain recursive count, not one of Lean's accelerated `Nat` operations.
Deciding that the count of a large `n` equals `n` takes the kernel time and
memory. -/
def slowCountD : Nat → Nat
  | 0 => 0
  | n + 1 => slowCountD n + 1

theorem fooD : True := by
  have _slow : slowCountD 40000 = 40000 := by decide
  trivial
