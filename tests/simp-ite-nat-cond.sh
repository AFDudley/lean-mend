#!/usr/bin/env bash
# rules/proposed/simp-ite-nat-cond.json on tests/fixtures/simp-ite-nat-cond, bumped from Lean v4.29.0 to
# v4.33.1: `simp [key, h]` leaves an `if` whose condition the hypothesis
# decides. The rule adds `← Nat.not_le` (condition `<`) or `← Nat.not_lt`
# (condition `≤`) to the simp.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run simp-ite-nat-cond
rule_fixture_checks simp-ite-nat-cond 2
src=$(cat "$app/App/Cond.lean")
grep -q 'simp \[checkLt, key, h, ← Nat.not_le\]' <<<"$src" \
  && pass "lt_revert: the simp gained ← Nat.not_le" || { failed "lt_revert"; echo "$src"; }
grep -q 'simp \[checkLe, key, h, ← Nat.not_lt\]' <<<"$src" \
  && pass "le_revert: the first candidate was rejected, the simp gained ← Nat.not_lt" || { failed "le_revert"; echo "$src"; }
report
