#!/usr/bin/env bash
# rules/proposed/simp-unsolved-simp-all.json on tests/fixtures/simp-unsolved-simp-all: the app moves from Lean
# v4.29.0 with dep v1 to v4.33.1 with dep v2, as the EquiVM adopt commit
# efbfb862 did. Dep v2 adds the simp lemma `toNat_lit64`, so `simp [h]`
# rewrites the literal in the goal before `h` can match, and the goal stays
# open. The rule appends `simp_all`. Lean then flags `h` unused in the simp,
# and lean-mend applies Lean's hint (docs/machine.md, structural check 4).
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/rule-fixture.sh"
fail=0
rule=simp-unsolved-simp-all
fx="$_lm_root/tests/fixtures/$rule"
work="$_lm_root/.scratch/rule-$rule"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
rm -rf "$work" && mkdir -p "$work/rules"
cp "$_lm_root/rules/proposed/$rule.json" "$work/rules/"
app="$work/app"
cp -r "$fx/app" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
at() {  # at <toolchain> <dep version>: the app's toolchain and dependency
  echo "leanprover/lean4:$1" > "$app/lean-toolchain"
  rm -rf "$app/dep" && cp -r "$fx/dep-$2" "$app/dep" && echo "leanprover/lean4:$1" > "$app/dep/lean-toolchain"
}
at v4.29.0 v1
git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app at v4.29.0 on dep v1"
at v4.33.1 v2
git -C "$app" add -A && git -C "$app" commit -q -m "bump to v4.33.1 and dep v2"
out=$("$bin" run "$app" --adopt --rules "$work/rules")
echo "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
rule_fixture_checks "$rule" 1
src=$(cat "$app/App/Cost.lean")
grep -Pzq '\n  simp\n  simp_all\n' <<<"$src" \
  && pass "simp_all follows the simp, and the unused h left the simp" || { failed "simp_all follows the simp without h"; echo "$src"; }
report
