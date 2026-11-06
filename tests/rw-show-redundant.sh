#!/usr/bin/env bash
# rules/proposed/rw-show-redundant.json on tests/fixtures/rw-show-redundant,
# bumped from Lean v4.29.0 on dep v1 to v4.33.1 on dep v2. Dep v2 adds simp
# lemmas for literal `toNat` values, so `simp [M]` already rewrites the
# literal and the `rw [show …]` after it finds nothing. The rule deletes that
# `rw`; the `rw [h]` after it stays.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run_dep rw-show-redundant
rule_fixture_checks rw-show-redundant 2
src=$(cat "$app/App/RwShow.lean")
! grep -q '^  rw \[show' <<<"$src" && [ "$(grep -c '^  rw \[h\]$' <<<"$src")" = 2 ] \
  && pass "both rw of a show term are deleted and both rw [h] stay" || { failed "both rw of a show term are deleted"; echo "$src"; }
report
