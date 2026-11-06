#!/usr/bin/env bash
# rules/proposed/heartbeat-raise.json on tests/fixtures/heartbeat-raise,
# bumped from Lean v4.29.0 on dep v1 to v4.33.1 on dep v2. Dep v2 makes the
# `simp` in App.Unroll cost more than the file's heartbeat limit. The rule's
# first candidate puts `set_option maxHeartbeats 400000 in` before the theorem,
# and the certificate check passes: the option is not part of the statement.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run_dep heartbeat-raise
rule_fixture_checks heartbeat-raise 1
src=$(cat "$app/App/Unroll.lean")
[ "$(grep -B1 '^theorem unroll' <<<"$src" | head -n 1)" = 'set_option maxHeartbeats 400000 in' ] \
  && pass "the first candidate, 400000, is before the theorem" || { failed "the first candidate, 400000, is before the theorem"; echo "$src"; }
report
