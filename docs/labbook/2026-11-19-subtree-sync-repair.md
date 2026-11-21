# 2026-11-19: repair of the standalone repository and the monorepo subtree

A hand-off note. It records what broke between lean-mend's standalone repository and
its copy in evm-proof-toolchain, what the repair did, and the work that is still open.

## The arrangement

lean-mend is a standalone repository with its own exophial instance. It is also a git
subtree of evm-proof-toolchain at `lean-mend/`. Work in the subtree goes upstream: after
each merge into evm-proof-toolchain, exophial's subtree sync (`exophial/subtree_sync.py`)
splits `lean-mend/` and reconciles it with this repository's `integrated` on GitHub.

## What broke

1. **The subtree lost the instance files.** evm-proof-toolchain commit `44664523`
   (2026-11-02) removed `.exophial/`, `.pebbles/`, `.claude/`, `repo_parameters.json`,
   `.pre-commit-config.yaml` and `contracts/` from `lean-mend/`. The operator ruled on
   2026-11-18 that this removal was wrong.
2. **The sync stopped pushing on 2026-11-07.** Every lean-mend sync after 02:52 that day
   ended in `conflict_preserved`, about 25 runs up to 2026-11-19 (records in
   evm-proof-toolchain `.exophial/logs/subtree-sync/lean-mend/`). No run pushed, and no
   one resolved a preserved conflict. GitHub `integrated` stayed at `f9de64a` while work
   continued in the subtree.
3. **The local checkout fell behind.** This checkout's `integrated` stayed at `74f877a`
   (2026-11-04), and 9 commits were made on it that GitHub did not have.

## What the repair did

All merges went through `exophial integrate --branch`.

| Repository | Commit | Change |
|---|---|---|
| lean-mend | `3e2aa6c1` | `.exophial/config.yaml` declares `integration_branch` (the installed exophial requires it). |
| lean-mend | `19313b35` | The gate image installs `binutils`, for `strings` in `tests/probe-source-tracked.sh`. |
| lean-mend | `e4491491` | A merge with three parents: this repository's `integrated` (`19313b35`), GitHub's `f9de64a`, and the split of the subtree at evm-proof-toolchain `74c607ea` (`899a4cd1`). Its tree is the split's tree with this repository's environment files. Local and GitHub `integrated` are both `e4491491`. |
| evm-proof-toolchain | `b2d2cd98` | `.exophial/config.yaml` declares `integration_branch`. |
| evm-proof-toolchain | `735c460f`, `06426581` | The subtree's instance files restored, and `bc430a8` (speculate width 4 by default) ported. |
| evm-proof-toolchain | `9e0bcefb` | `setupTreeLimit` tests cgroup v2's No Internal Process Constraint before it writes (`LeanMend/Shell/Memory.lean`, `canEnableController`). The gate failed as root in this repository's container without it. |
| evm-proof-toolchain | `74c607ea` | A subtree marker with all three trailers. `735c460f`, `06426581` and `9e0bcefb` carried only `git-subtree-dir`, and the sync refused a marker with no base. |

## Rules learned

- A commit in evm-proof-toolchain that edits `lean-mend/` carries three trailers, copied
  from the newest valid marker: `git-subtree-dir`, `git-subtree-mainline` and
  `git-subtree-split`. The commit-msg hook checks only the first one, but the sync needs
  all three (`check_sync_precondition`).
- A `conflict_preserved` sync is an open defect, not a log line. It must be resolved
  before the next change, or the two copies drift further apart.
- Fetch and fast-forward this checkout from GitHub before committing in it.
- exophial rebases a branch onto `integrated`. A branch that holds a merge commit must
  therefore be based on the current tip, so the merge is a fast-forward (INV-112).

## Open work

1. **The next sync is not yet observed.** No evm-proof-toolchain merge has happened since
   `e4491491` reached GitHub. The next one starts a lean-mend sync. Its record in
   `.exophial/logs/subtree-sync/lean-mend/` must say `synced`, and it should bring the
   `binutils` line and the `integration_branch` line down into `lean-mend/`.
2. **GitHub `main` is at `f9de64a`.** It has not moved to `e4491491`.
3. **An unconfirmed runtime report.** The worker that fixed the cgroup check reported,
   from `strace`, that a failed write to `cgroup.subtree_control` (EBUSY) did not raise an
   exception in Lean's `IO.FS.writeFile`. No minimal reproduction exists yet.
4. **Local branches and worktrees left from the repair:** `repair/clean-history` to
   `repair/clean-history5`, `env/config-line`, `env/gate-binutils`, `env/gate-binutils2`,
   and their worktrees under `.scratch/`.
