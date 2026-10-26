/-! S4 (`docs/parallel.md` P14-P16): `tests/speculate.sh` runs lean-mend with
the rules in `rules/`, in file-name (rule) order. The first two rules leave
the site open and add a slow, decided computation after it, so their
worktree's rebuild takes noticeably longer. The third rule fixes the site and
is fast. The run speculates all three candidates at the same time, so the
fast fix often finishes before the slow rejects do, and the Core must still
accept the third candidate, in rule order (P15), not the first to finish. -/
set_option maxRecDepth 1000000

/-- A plain recursive count, not one of Lean's accelerated `Nat` operations.
Deciding `slowCount n = n` for a large `n` takes the kernel noticeably longer
than a small one, so a candidate that keeps this call open makes its own
rebuild slower, with no effect on any other candidate's rebuild. -/
def slowCount : Nat → Nat
  | 0 => 0
  | n + 1 => slowCount n + 1

theorem foo : True := by
  exact unknownHead
