#!/usr/bin/env bash
# rules/proposed/simpa-using-bang-nested.json on tests/fixtures/simpa-using-bang-nested, bumped
# from Lean v4.29.0 to v4.33.1, with rules/proposed/simpa-close-transparency.json
# beside it. A `simpa … using` term holds a `by simpa … using h` block, and
# both closes need default transparency (EquiVM
# Examples.OpenZeppelinBench.ERC6909.SetOperator 44-49). `using!` on the
# inner simpa alone lets Lean report the outer one at an earlier position, so
# that candidate is rejected; the nested candidate writes `using!` in both, in
# one edit, and the run must end done.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
work="$root/.scratch/rule-simpa-using-bang-nested"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
rm -rf "$work" && mkdir -p "$work/rules"
# The rule files themselves, not copies kept in the fixture.
cp "$root/rules/proposed/simpa-close-transparency.json" "$root/rules/proposed/simpa-using-bang-nested.json" "$work/rules/"
app="$work/app"
cp -r "$root/tests/fixtures/simpa-using-bang-nested" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
g add -A && g commit -q -m "bump to v4.33.1"
out=$("$bin" run "$app" --adopt --rules "$work/rules")
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fi
}
check "the run ends done, with no residue" '.state == "done" and .residue == []' "$out"
check "the bump breaks one site, the inner simpa, typeMismatch" \
  '[.[] | select(.obs == "diagnosed") | .detail.detail[] | [.class, .line]] == [["LeanMend.ErrorClass.typeMismatch", 32]]' "$ledger"
check "using! on the inner simpa alone leaves 1 error; the nested candidate leaves 0" \
  '[.[] | select(.obs == "rebuilt") | [.detail.rule, .detail.errors, .detail.lint]] ==
     [["simpa-close-transparency: LeanMend.EditOp.simpaUsingBang", 1, 0],
      ["simpa-using-bang-nested: LeanMend.EditOp.simpaUsingBangNested", 0, 0]]' "$ledger"
src=$(cat "$app/App/Nested.lean")
grep -q 'simpa only \[Word.add_assoc\]$' <<<"$src" && grep -q '    using! lift (by simpa only \[Word.add_assoc\] using! h)' <<<"$src" \
  && pass "both simpas close with using!, and the layout is kept" || { failed "source"; echo "$src"; }
subjects=$(g log --format=%s main..lean-mend/mend)
[ "$subjects" = "lean-mend: simpa-using-bang-nested: LeanMend.EditOp.simpaUsingBangNested in App.Nested" ] \
  && pass "one commit on lean-mend/mend, the nested candidate" || { failed "commits"; echo "$subjects"; }
(cd "$app" && lake build -q >/dev/null) && pass "the mended app builds at v4.33.1" || failed "the mended app builds at v4.33.1"
report
