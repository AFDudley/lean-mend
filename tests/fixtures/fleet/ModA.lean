/-! S3b (`docs/parallel.md` P8, P10-P12): `tests/fleet.sh` breaks `ModA` and
`ModB` in one commit. Neither module imports the other, so both mends start
at once. `ModA`'s accepted fix makes the kernel decide a plain recursive
count, so its attempt takes noticeably longer than `ModB`'s: the parallel
driver must still replay `ModA` and `ModB` in the ledger and the mend-branch
commits in their canonical (topological) order, not in the order their
worktrees finish. -/
set_option maxRecDepth 1000000

/-- A plain recursive count, not one of Lean's accelerated `Nat` operations
(the same device as `tests/fixtures/speculate/App.lean`'s `slowCount`).
Deciding `slowCountA n = n` for a large `n` takes the kernel noticeably
longer than a small one. -/
def slowCountA : Nat → Nat
  | 0 => 0
  | n + 1 => slowCountA n + 1

theorem fooA : True := by
  exact unknownHeadA
