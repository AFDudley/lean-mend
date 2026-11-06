/-! `tests/probe-bound.sh` (`docs/parallel.md` P24): one of four independent
modules, each with one break. The first candidate of the rule keeps the break
and adds a slow decided count, so the Core rejects it. The second candidate
fixes the break and also adds a slow count. So each module holds its probe
for two slow attempts, and the four mends overlap when the memory limit
admits them. -/
set_option maxRecDepth 1000000

/-- A plain recursive count, not one of Lean's accelerated `Nat` operations
(the device of `tests/fixtures/fleet/ModA.lean`). -/
def slowCountB : Nat → Nat
  | 0 => 0
  | n + 1 => slowCountB n + 1

theorem fooB : True := by
  have _slow : slowCountB 40000 = 40000 := by decide
  trivial
