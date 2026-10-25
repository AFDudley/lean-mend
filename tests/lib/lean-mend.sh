# Builds lean-mend and sets $bin to the binary (docs/process.md § Check
# scripts). A runner that runs lean-mend sources this file, so the runner
# works alone: in a fresh worktree, or alone in exophial's gate container,
# where no earlier step built the binary. `lake build` is incremental, so a
# second build costs little. Build output goes to stderr.
_lm_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
(cd "$_lm_root" && lake build lean-mend >&2)
bin="$_lm_root/.lake/build/bin/lean-mend"
