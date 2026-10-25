#!/usr/bin/env bash
# The lean-mend commit gate (docs/process.md § Repository gates).
# exophial runs it in the branch worktree before every merge
# (.exophial/config.yaml, gate.command). Each step fails loud.
#
# stdout carries one JSON object and nothing else, so an exophial spec can
# observe it (`stdout_json`): {"steps": [{"name", "ok"}...], "passed", "failed"}.
# Every step's own output goes to stderr. The gate stops at the first failed
# step; that step is the last entry, with "ok": false.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
exec 3>&1 1>&2

steps=()
passed=0
summary() {
  local IFS=,
  printf '{"steps":[%s],"passed":%d,"failed":%d}\n' "${steps[*]}" "$passed" "$1" >&3
}
# step NAME COMMAND...: run COMMAND; on failure, print the summary and exit 1.
step() {
  local name=$1; shift
  echo "== $name"
  if "$@"; then
    steps+=("{\"name\":\"$name\",\"ok\":true}"); passed=$((passed + 1))
  else
    steps+=("{\"name\":\"$name\",\"ok\":false}"); summary 1; exit 1
  fi
}

boundary() {
  if grep -rnE '^import LeanMend\.Shell' LeanMend/Spec LeanMend/Core; then
    echo "FAIL: a Spec or Core module imports the shell"; return 1
  fi
}
build() { lake build && lake build lean-mend; }

step "boundary: Spec and Core import no Shell module (concept A2)" boundary
step "lake build" build
step "no LeanMend constant depends on sorryAx (docs/verification.md)" lake env lean tests/NoSorry.lean
step "lake test" lake test
step "probe matrix" tests/probe-matrix.sh
step "lean-mend baseline on a real target" tests/baseline.sh
step "lean-mend run --adopt on the rename fixture" tests/rename.sh
step "lean-mend run --adopt --rules on the simp-set fixture" tests/simpset.sh
step "decision D11 on the binder fixture" tests/binder.sh
step "decision D12 on the follow fixture" tests/follow.sh
step "site order by declaration coordinates" tests/order.sh tests/fixtures/order-first
step "a namespace move with no aliases, on the move fixture" tests/move.sh
summary 0
