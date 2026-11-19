#!/usr/bin/env bash
# rules/proposed/simp-set-pure-unsolved.json on tests/fixtures/simp-set-pure-unsolved, bumped from Lean v4.29.0 to
# v4.33.1: `simp [Res.bind, bind]` leaves `match pure 0, f` unsolved. The
# rule adds `pure` to the simp.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run simp-set-pure-unsolved
rule_fixture_checks simp-set-pure-unsolved 1
grep -q 'simp \[gt0, lit, bind, Res.bind, pure\]' "$app/App/Pure.lean" \
  && pass "the simp gained pure" || { failed "the simp gained pure"; cat "$app/App/Pure.lean"; }
report
