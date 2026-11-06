#!/usr/bin/env bash
# rules/proposed/simp-no-progress-delete.json on tests/fixtures/simp-no-progress-delete,
# bumped from Lean v4.29.0 to v4.33.1: `simp only [stk] at h3`, where the
# unifier already unfolded `stk`, gave only an unused-argument warning at
# v4.29.0 and is the error "`simp` made no progress" at v4.33.1. The rule
# deletes that simp.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run simp-no-progress-delete
rule_fixture_checks simp-no-progress-delete 2
src=$(cat "$app/App/Stack.lean")
! grep -q '^  simp only \[stk\] at h3$' <<<"$src" && [ "$(grep -c '^  exact h3$' <<<"$src")" = 2 ] \
  && pass "both simp only [stk] are deleted and both exact h3 stay" || { failed "both simp only [stk] are deleted"; echo "$src"; }
report
