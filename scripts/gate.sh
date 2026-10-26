#!/usr/bin/env bash
# The lean-mend commit gate (docs/process.md § Repository gates).
# exophial runs it in the branch worktree before every merge
# (.exophial/config.yaml, gate.command). Each step fails loud.
#
# stdout carries one JSON object and nothing else, so an exophial spec can
# observe it (`stdout_json`): one key "steps.<step name>.ok" per step that
# ran, then "passed" and "failed". exophial reads a whole field path as a
# top-level key first, so `steps.<step name>.ok` resolves even when the name
# holds a dot. Every step's own output goes to stderr. The gate stops at the
# first failed step; that step is the last key, with value false.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
exec 3>&1 1>&2

_obj='{}'
passed=0
# record NAME OK: add the key "steps.NAME.ok" to the result object.
record() { _obj=$(jq -cn --argjson o "$_obj" --arg k "steps.$1.ok" --argjson v "$2" '$o + {($k): $v}'); }
# summary FAILED: print the result object, then the counts, on stdout.
summary() {
  jq -cn --argjson o "$_obj" --argjson p "$passed" --argjson f "$1" '$o + {passed: $p, failed: $f}' >&3
}
# step NAME COMMAND...: run COMMAND; on failure, print the summary and exit 1.
step() {
  local name=$1; shift
  echo "== $name"
  if "$@"; then
    record "$name" true; passed=$((passed + 1))
  else
    record "$name" false; summary 1; exit 1
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
step "D12 body edit and statement follow as one candidate" \
  tests/follow-pair.sh tests/fixtures/follow-pair
step "site order by declaration coordinates" tests/order.sh tests/fixtures/order-first
step "speculation across candidates" tests/speculate.sh
exposure() {
  [ "$(tests/expose.sh tests/fixtures/expose-two | jq -r .verdict)" = accepted ] &&
  [ "$(tests/expose.sh tests/fixtures/expose-back | jq -r .verdict)" = rejected ]
}
step "exposure of later errors" exposure
step "a namespace move with no aliases, on the move fixture" tests/move.sh
summary 0
