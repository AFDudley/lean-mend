#!/usr/bin/env bash
# rules/proposed/rw-unsolved-simp-all.json on tests/fixtures/rw-unsolved-simp-all, bumped from Lean v4.29.0 to
# v4.33.1: `simp only [..., Fin.toNat, if_pos h]` unfolds `Fin.toNat` in an
# `if` condition but not in its `Decidable` instance, so `if_pos h` no longer
# rewrites the `if`, and the goal after the `rw` stays open. The rule appends
# `simp_all` after the `rw`.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule_fixture_run rw-unsolved-simp-all
rule_fixture_checks rw-unsolved-simp-all 1
src=$(cat "$app/App/Ite.lean")
grep -Pzq '  rw \[Nat\.add_zero\]\n  simp_all\n' <<<"$src" \
  && pass "simp_all follows the rw on its own line" || { failed "simp_all follows the rw"; echo "$src"; }
report
