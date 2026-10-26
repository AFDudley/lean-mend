/-! S3b (`docs/parallel.md` P8, P10-P12): `tests/fleet.sh` breaks `ModA` and
`ModB` in one commit. Neither module imports the other, so both become
frontier modules in the same wave. `ModA`'s accepted fix makes the kernel
decide a plain recursive count, so its wave attempt takes noticeably longer
than `ModB`'s: the parallel driver must still replay `ModA` before `ModB` in
the ledger and the mend-branch commits whenever that is their canonical
(topological) order, not whichever module's worktree finishes first. -/
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
