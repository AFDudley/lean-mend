#!/usr/bin/env bash
# rules/proposed/simp-set-pure-mismatch.json on tests/fixtures/simp-set-pure-mismatch, bumped from
# Lean v4.29.0 to v4.33.1: `simp only [gt0, bind]` leaves `match pure 0, f`,
# so `simpa [Res.bind] using h` fails with "Type mismatch: After
# simplification" (EquiVM Examples.UniswapV2Pair.UpdateSource 131). The rule
# adds `pure` to the simpa.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run simp-set-pure-mismatch
rule_fixture_checks simp-set-pure-mismatch 1
if jq -e '[.[] | select(.obs == "diagnosed") | .detail.detail[].class] == ["LeanMend.ErrorClass.typeMismatch"]' <<<"$ledger" >/dev/null
then pass "the site is typeMismatch"; else failed "the site is typeMismatch"; fi
grep -q 'simpa \[Res.bind, pure\] using h' "$app/App/Pure.lean" \
  && pass "the simpa gained pure" || { failed "the simpa gained pure"; cat "$app/App/Pure.lean"; }
report
