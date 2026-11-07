#!/usr/bin/env bash
# Runs `lean-mend baseline` against tests/fixtures/probe-basic under a toolchain
# other than lean-mend's own, once intact and once broken.
# See docs/machine.md § Transitions (baseline) and docs/architecture.md.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
work="$root/.scratch/baseline"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}

rm -rf "$work" && mkdir -p "$work"
cp -r "$root/tests/fixtures/probe-basic/." "$work/"
echo "leanprover/lean4:v4.33.1" > "$work/lean-toolchain"

out=$("$bin" baseline "$work")
check "intact target is baselined" '.state == "baselined"' "$out"
check "graph order" '.order == ["Fx.Basic", "Fx.Uses", "Fx"]' "$out"
check "certificate rows: 13 declarations (an axiom among them) and 3 types, no generated ones" '(.decls | length) == 16 and ([.decls[].name] | index("Fx.instReprPt") == null) and ([.decls[].name] | (index("Fx.Pt") != null) and (index("Fx.Color") != null) and (index("Fx.HasZero") != null) and (index("Fx.zero_eq_zero") != null))' "$out"
check "axioms in the certificate" \
  '.decls[] | select(.name == "Fx.em_use") | .axioms | index("Classical.choice") != null' "$out"

sed -i 's/:= n + n/:= Old.g n/' "$work/Fx/Basic.lean"
out=$("$bin" baseline "$work" || true)
check "broken target halts with baselineRed" '.state | startswith("halted LeanMend.Refusal.baselineRed")' "$out"
check "importers of a broken module are not built" '.failing == ["Fx.Basic", "Fx.Uses", "Fx"] and (.decls | length) == 0' "$out"

# Two modules that declare the same name (`main` of two executables) build one by
# one, but Lean cannot import both into one environment. The certificate must
# still read both, so the probe splits such a chunk instead of halting the run.
rm -rf "$work" && mkdir -p "$work"
cp -r "$root/tests/fixtures/probe-clash/." "$work/"
echo "leanprover/lean4:v4.33.1" > "$work/lean-toolchain"
out=$("$bin" baseline "$work")
check "a target whose modules clash is baselined" '.state == "baselined"' "$out"
check "certificate rows from both clashing modules" '([.decls[] | select(.name == "main")] | length) == 2 and ([.decls[].name] | (index("Cx.a_self") != null) and (index("Cx.b_self") != null))' "$out"
report
