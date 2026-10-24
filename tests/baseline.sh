#!/usr/bin/env bash
# Runs `lean-mend baseline` against tests/fixtures/probe-basic under a toolchain
# other than lean-mend's own, once intact and once broken.
# See docs/machine.md § Transitions (baseline) and docs/architecture.md.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/.lake/build/bin/lean-mend"
work="$root/.scratch/baseline"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then echo "ok   $1"; else echo "FAIL $1"; echo "$3"; fail=1; fi
}

rm -rf "$work" && mkdir -p "$work"
cp -r "$root/tests/fixtures/probe-basic/." "$work/"
echo "leanprover/lean4:v4.33.1" > "$work/lean-toolchain"

out=$("$bin" baseline "$work")
check "intact target is baselined" '.state == "baselined"' "$out"
check "graph order" '.order == ["Fx.Basic", "Fx.Uses", "Fx"]' "$out"
check "certificate rows: the 10 source declarations, no generated ones" '(.decls | length) == 10 and ([.decls[].name] | index("Fx.instReprPt") == null)' "$out"
check "axioms in the certificate" \
  '.decls[] | select(.name == "Fx.em_use") | .axioms | index("Classical.choice") != null' "$out"

sed -i 's/:= n + n/:= Old.g n/' "$work/Fx/Basic.lean"
out=$("$bin" baseline "$work" || true)
check "broken target halts with baselineRed" '.state | startswith("halted LeanMend.Refusal.baselineRed")' "$out"
check "importers of a broken module are not built" '.failing == ["Fx.Basic", "Fx.Uses", "Fx"] and (.decls | length) == 0' "$out"
exit $fail
