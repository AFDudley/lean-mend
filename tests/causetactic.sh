#!/usr/bin/env bash
# tests/causetactic.sh: the probe's `causeTactic` command
# (docs/machine.md § The tactic inside the site; docs/rules.md §
# Axiom-finding rules), on tests/fixtures/causetactic-congr. `xs` is a free
# variable, so `Array.any` cannot compute: the only way to prove
# `App.useDefn` is Lean core's `Array.any_congr` (`@[congr]`), which needs
# `p` and `target` equal pointwise, under `Array.any`'s own binder over the
# array's elements. `simp only [defn]` closes that pointwise goal, so
# `Array.any_congr` is in the assembled proof. Checks: `causeTactic` on
# `App.useDefn` and `Array.any_congr` returns the `simp only [defn]` node;
# on a constant no tactic of the declaration uses, it returns `null`.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
fx="$root/tests/fixtures/causetactic-congr"
work="$root/.scratch/causetactic"
tc="leanprover/lean4:v4.33.1"
fail=0

rm -rf "$work" && mkdir -p "$work"
cp -r "$fx/." "$work/"
echo "$tc" > "$work/lean-toolchain"
cp "$root/probe/Probe.lean" "$work/Probe.lean"
(cd "$work" && lake build -q >/dev/null)

run() { (cd "$work" && lake env lean --run Probe.lean "$@"); }
offset=$(grep -bo 'theorem useDefn' "$work/App.lean" | cut -d: -f1)

hit=$(run causeTactic App.lean "$offset" Array.any_congr)
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}
check "causeTactic on Array.any_congr returns a node" '.node != null' "$hit"
check "the node is a simp tactic" '.node.kind == "Lean.Parser.Tactic.simp"' "$hit"
check "the node's tokens are simp only [defn]" \
  '[.node.tokens[].text] == ["simp", "only", "[", "defn", "]"]' "$hit"

miss=$(run causeTactic App.lean "$offset" App.nope)
check "causeTactic on a constant no tactic uses returns null" '.node == null' "$miss"

report
