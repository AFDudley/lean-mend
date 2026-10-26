#!/usr/bin/env bash
# S3a of docs/parallel.md: `tests/OpsTest.lean` proves the fleet of Mending
# states (the order test), and `tests/NoSorry.lean` proves no LeanMend
# constant depends on `sorryAx`.
#
# stdout carries one JSON object and nothing else, so an exophial spec can
# observe it (`stdout_json`): {"lake_test_exit", "nosorry_exit"}. Each
# check's own output goes to stderr.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
exec 3>&1 1>&2

lake test
lake_test_exit=$?

lake env lean tests/NoSorry.lean
nosorry_exit=$?

printf '{"lake_test_exit":%d,"nosorry_exit":%d}\n' "$lake_test_exit" "$nosorry_exit" >&3
