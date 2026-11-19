#!/usr/bin/env bash
# rules/proposed/rw-proof-arg-erw.json on tests/fixtures/rw-proof-arg-erw, bumped from Lean v4.29.0 to
# v4.33.1: `rw` no longer assigns a structure's proof field to the
# lemma's proof argument of a definitionally equal type. The rule makes it `erw`.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run rw-proof-arg-erw
rule_fixture_checks rw-proof-arg-erw 2
[ "$(grep -c '^  erw \[load_01 ' "$app/App/Field.lean")" = 2 ] \
  && pass "both rw became erw" || { failed "both rw became erw"; cat "$app/App/Field.lean"; }
report
