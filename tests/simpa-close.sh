#!/usr/bin/env bash
# The rule rules/proposed/simpa-close-transparency.json on
# tests/fixtures/simpa-close, bumped from Lean v4.29.0 to v4.33.1. From
# v4.31.0 (#13636) `simpa … using h` closes at reducible transparency, so two
# `simpa only [Word.add_assoc] using hwf.d3` proofs fail with "Type mismatch:
# After simplification" (EquiVM Reasoning.SolcRoutines 1464 has the same
# shape). The rule's one candidate, `simpaUsingBang`, writes `using!`, the
# close at default transparency, and the run must end done.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
work="$root/.scratch/simpa-close"
rule=simpa-close-transparency
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work/rules"
# The rule file itself, not a copy kept in the fixture.
cp "$root/rules/proposed/$rule.json" "$work/rules/"
app="$work/app"
cp -r "$root/tests/fixtures/simpa-close" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
g add -A && g commit -q -m "bump to v4.33.1"

out=$("$bin" run "$app" --adopt --rules "$work/rules")
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
check "the run ends done, with no residue" '.state == "done" and .residue == []' "$out"
check "App.Close: the bump breaks two simpa proofs, both typeMismatch" \
  'map(select(.obs == "diagnosed" and .detail.module == "App.Close"))[0].detail.detail | map(.class) ==
     ["LeanMend.ErrorClass.typeMismatch", "LeanMend.ErrorClass.typeMismatch"]' "$ledger"
check "the simpaUsingBang candidate was accepted at each site (errors 2 → 1 → 0)" \
  "[.[] | select(.obs == \"rebuilt\") | [.detail.rule, .detail.errors, .detail.lint]] ==
     [[\"$rule: LeanMend.EditOp.simpaUsingBang\", 1, 0], [\"$rule: LeanMend.EditOp.simpaUsingBang\", 0, 0]]" "$ledger"
src=$(cat "$app/App/Close.lean")
[ "$(grep -c 'simpa only \[Word.add_assoc\] using! hwf.d3' <<<"$src")" = 2 ] && ! grep -q ' using hwf.d3' <<<"$src" \
  && pass "both proofs are simpa … using! hwf.d3, and the simp set is kept" || { failed "source"; echo "$src"; fail=1; }
n=$(g rev-list --count main..lean-mend/mend)
[ "$n" = 2 ] && pass "two commits on lean-mend/mend" || { failed "commits: $n"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && pass "the mended app builds at v4.33.1" || { failed "build"; fail=1; }
report
