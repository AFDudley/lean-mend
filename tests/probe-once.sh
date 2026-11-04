#!/usr/bin/env bash
# tests/probe-once.sh <fixture>: S0a (docs/parallel.md C1). Runs a full mend
# with the current lean-mend and checks the ledger holds exactly one probe
# start for the module, then checks that the mended branch's tree equals the
# tree of the same run with the lean-mend binary from before this slice (the
# `integrated` branch).
#
# stdout carries one JSON object and nothing else:
# {"probe_starts": N, "tree_equal": true|false}.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="${1:?usage: tests/probe-once.sh <fixture>}"
work="$root/.scratch/probe-once"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work"
mkdir -p "$work"

setup_app() {  # setup_app <dir>
  local app="$1"
  mkdir -p "$app"
  cp "$fx/lakefile.toml" "$app/lakefile.toml"
  cat "$root/lean-toolchain" > "$app/lean-toolchain"
  printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
  cat > "$app/App.lean" << 'EOF'
theorem placeholder : True := by trivial
EOF
  git -C "$app" init -q -b main
  git -C "$app" add -A
  git -C "$app" commit -q -m "app builds"
  cp "$fx/App.lean" "$app/App.lean"
  git -C "$app" add -A
  git -C "$app" commit -q -m "break foo"
}

run_fixture() {  # run_fixture <binary> <appdir> : prints the mend branch's tree
  local binp="$1" app="$2"
  setup_app "$app" >&2
  "$binp" run "$app" --adopt --rules "$fx/rules" >&2
  git -C "$app" rev-parse lean-mend/mend^{tree}
}

new_app="$work/new"
new_tree=$(run_fixture "$bin" "$new_app")
probe_starts=$(jq -s '[.[] | select(.obs == "probeStart" and .detail.module == "App")] | length' \
  "$new_app/.lean-mend/ledger.jsonl")

old_src="$work/old-src"
git -C "$root" worktree add -q --detach "$old_src" integrated
(cd "$old_src" && lake build lean-mend -q) >&2
old_bin="$old_src/.lake/build/bin/lean-mend"
old_app="$work/old"
old_tree=$(run_fixture "$old_bin" "$old_app")
git -C "$root" worktree remove --force "$old_src"

tree_equal=false
[ "$new_tree" = "$old_tree" ] && tree_equal=true

jq -nc --argjson p "$probe_starts" --argjson t "$tree_equal" '{probe_starts: $p, tree_equal: $t}'
[ "$probe_starts" -eq 1 ] && [ "$tree_equal" = true ]
