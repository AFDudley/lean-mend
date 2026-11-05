#!/usr/bin/env bash
# rules/proposed/simp-set-pure-prior.json on tests/fixtures/simp-set-pure-prior, bumped from Lean v4.29.0 to
# v4.33.1: `simp only [bind, Option.bind]` leaves `match pure x, f`, so the
# `apply` and the `rw` after it fail. The rule adds `pure` to that simp.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run simp-set-pure-prior
rule_fixture_checks simp-set-pure-prior 2
src=$(cat "$app/App/Pure.lean")
[ "$(grep -c 'simp only \[toWord, bind, Option.bind, pure\]' <<<"$src")" = 2 ] \
  && pass "both simps before the failing tactics gained pure" || { failed "both simps gained pure"; echo "$src"; }
report
