#!/usr/bin/env bash
# The lean-mend commit gate (docs/process.md § Repository gates).
# exophial runs it in the branch worktree before every merge
# (.exophial/config.yaml, gate.command). Each step fails loud.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== boundary: Spec and Core import no Shell module (concept A2)"
if grep -rnE '^import LeanMend\.Shell' LeanMend/Spec LeanMend/Core; then
  echo "FAIL: a Spec or Core module imports the shell"; exit 1
fi

echo "== lake build"
lake build
lake build lean-mend

echo "== no LeanMend constant depends on sorryAx (docs/verification.md)"
lake env lean tests/NoSorry.lean

echo "== lake test"
lake test

echo "== probe matrix"
tests/probe-matrix.sh

echo "== lean-mend baseline on a real target"
tests/baseline.sh
