#!/usr/bin/env bash
# tests/static-diff-export.sh: the probe's `export` command
# (docs/static-diff.md § 1, slice 1), on tests/fixtures/static-diff-export.
# `dep` is a Lean-core-only package (no Mathlib), committed as two
# revisions: v1 at Lean v4.29.0, v2 at Lean v4.33.1.
#
# Acceptance (slice 1): the export at each side lists a lemma that gains
# `Classical.choice` (`Dep.f_congr`) and a lemma that moves to another
# module (`Dep.f_pos`, `Dep.Basic` to `Dep.Pos`). This also checks
# `erasedBody`: `Dep.f_congr` is a `theorem`, so its whole body is a proof
# and `export` erases it to the same placeholder at both sides, despite the
# axiom gain — the axiom set is the signal that changed, not the body.
# `Dep.usesProof` is an unchanged `def` whose value embeds a proof
# subterm: the two sides give the identical erased body, with the proof
# argument replaced and the data argument kept.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
fx="$root/tests/fixtures/static-diff-export"
work="$root/.scratch/static-diff-export"
fail=0

rm -rf "$work" && mkdir -p "$work/v1" "$work/v2"
cp -r "$fx/dep-v1/." "$work/v1/"
echo "leanprover/lean4:v4.29.0" > "$work/v1/lean-toolchain"
cp "$root/probe/Probe.lean" "$work/v1/Probe.lean"
cp -r "$fx/dep-v2/." "$work/v2/"
echo "leanprover/lean4:v4.33.1" > "$work/v2/lean-toolchain"
cp "$root/probe/Probe.lean" "$work/v2/Probe.lean"
(cd "$work/v1" && lake build -q >/dev/null)
(cd "$work/v2" && lake build -q >/dev/null)

(cd "$work/v1" && lake env lean --run Probe.lean export Dep) > "$work/v1.ndjson"
(cd "$work/v2" && lake env lean --run Probe.lean export Dep) > "$work/v2.ndjson"

check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}

# Lean core and Std dwarf the dependency, so grep out each target constant's
# own line before jq parses it: jq's parser depth limit rejects some of the
# deeply nested Init/Grind proof terms in the full export.
line() { grep -F "\"const\":\"$2\"" "$1"; }  # line <ndjson file> <const>

f_congr_v1=$(line "$work/v1.ndjson" Dep.f_congr)
f_congr_v2=$(line "$work/v2.ndjson" Dep.f_congr)
check "Dep.f_congr has no axiom at v4.29.0" '.axioms == []' "$f_congr_v1"
check "Dep.f_congr gains Classical.choice at v4.33.1" \
  '.axioms | index("Classical.choice") != null' "$f_congr_v2"
check "Dep.f_congr stays in Dep.Basic at both sides" \
  '.v1.module == "Dep.Basic" and .v2.module == "Dep.Basic"' \
  "$(jq -cn --argjson v1 "$f_congr_v1" --argjson v2 "$f_congr_v2" '{v1: $v1, v2: $v2}')"
check "Dep.f_congr's whole body is a proof, erased to the same placeholder at both sides" \
  '.v1.body == "#" and .v2.body == "#"' \
  "$(jq -cn --argjson v1 "$f_congr_v1" --argjson v2 "$f_congr_v2" '{v1: $v1, v2: $v2}')"

f_pos_v1=$(line "$work/v1.ndjson" Dep.f_pos)
f_pos_v2=$(line "$work/v2.ndjson" Dep.f_pos)
check "Dep.f_pos is in Dep.Basic at v4.29.0" '.module == "Dep.Basic"' "$f_pos_v1"
check "Dep.f_pos moves to Dep.Pos at v4.33.1" '.module == "Dep.Pos"' "$f_pos_v2"

up_v1=$(line "$work/v1.ndjson" Dep.usesProof)
up_v2=$(line "$work/v2.ndjson" Dep.usesProof)
check "Dep.usesProof's erased body is identical at both sides (unchanged def, comparable form)" \
  '.v1.body == .v2.body' \
  "$(jq -cn --argjson v1 "$up_v1" --argjson v2 "$up_v2" '{v1: $v1, v2: $v2}')"
check "Dep.usesProof's erased body keeps the data argument as a real subterm, not a placeholder" \
  '.body.lam.body.lam.body != "#"' "$up_v1"
check "Dep.usesProof's erased body replaces the proof argument with the placeholder" \
  '[.. | strings] | index("#") != null' "$up_v1"

report
