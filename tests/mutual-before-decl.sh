#!/usr/bin/env bash
# Decision D17: `beforeDecl`'s insertion point is the enclosing `mutual`'s
# own start, not the member declaration's own start, when the site is a
# member of a `mutual` block.
#
# tests/fixtures/mutual-before-decl/ is tests/fixtures/heartbeat-raise/,
# with `unroll` made a member of a two-theorem `mutual` block, alongside a
# second theorem `companion`. The bump from dep v1 (Lean v4.29.0) to dep v2
# (Lean v4.33.1) breaks `unroll`'s `simp` the same way; because a `mutual`
# block elaborates as one command with one heartbeat budget, the timeout
# also hits `companion`, so the bump diagnoses 2 sites, not 1.
# rules/proposed/heartbeat-raise.json's first candidate puts
# `set_option maxHeartbeats 400000 in` before the site.
#
# `set_option … in` before one member of a `mutual` block is a parse error
# in the whole block (measured at v4.33.1 on a standalone fixture,
# `.scratch/ax-s4-measure/App2.lean` in this worktree): "invalid mutual
# block: either all elements of the block must be inductive/structure
# declarations, or they must all be definitions/theorems/abbrevs". Before
# decision D17's fix, every candidate on this site causes that error and is
# rejected, so the run ends with residue. After the fix, the candidate goes
# before `mutual` (`App3.lean` in the same measurement), the run ends done
# with no residue, and the mended app builds at v4.33.1.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"

root="$_lm_root"
rule=heartbeat-raise
fx="$root/tests/fixtures/mutual-before-decl"
work="$root/.scratch/mutual-before-decl"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
rm -rf "$work" && mkdir -p "$work/rules"
app="$work/app"
cp -r "$fx/app" "$app"
cp "$root/rules/proposed/$rule.json" "$work/rules/"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
_at() {  # _at TOOLCHAIN DEP
  echo "leanprover/lean4:$1" > "$app/lean-toolchain"
  rm -rf "$app/dep" && cp -r "$fx/dep-$2" "$app/dep" && echo "leanprover/lean4:$1" > "$app/dep/lean-toolchain"
}
_at v4.29.0 v1
git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app at v4.29.0"
_at v4.33.1 v2
git -C "$app" add -A && git -C "$app" commit -q -m "bump to v4.33.1 and dep v2"
out=$("$bin" run "$app" --adopt --rules "$work/rules")
echo "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")

if jq -e '[.[] | select(.obs == "diagnosed") | .detail.detail | length] | first == 2' <<<"$ledger" >/dev/null
then pass "the bump to v4.33.1 breaks 2 sites: unroll's simp, and companion sharing its heartbeat budget"
else failed "the bump to v4.33.1 breaks 2 sites: unroll's simp, and companion sharing its heartbeat budget"; fi
if jq -e '.state == "done" and .residue == []' <<<"$out" >/dev/null
then pass "the run is done with no residue on a mutual-nested site"
else failed "the run is done with no residue on a mutual-nested site"; fi
subjects=$(git -C "$app" log --format=%s main..lean-mend/mend)
if [ "$(grep -c "^lean-mend: $rule: " <<<"$subjects")" = 1 ] && [ "$(wc -l <<<"$subjects")" = 1 ]
then pass "the mend branch holds 1 commit, a candidate of $rule"
else failed "the mend branch holds 1 commit, a candidate of $rule"; echo "$subjects"; fi
if (cd "$app" && lake build -q >/dev/null)
then pass "the mended app builds at v4.33.1"; else failed "the mended app builds at v4.33.1"; fi
src=$(cat "$app/App/Unroll.lean")
if [ "$(grep -B1 '^mutual' <<<"$src" | head -n 1)" = 'set_option maxHeartbeats 400000 in' ]
then pass "the candidate goes before the mutual keyword, not before unroll"
else failed "the candidate goes before the mutual keyword, not before unroll"; echo "$src"; fi
if ! grep -q '^set_option maxHeartbeats 400000 in\s*$' <<<"$(grep -B1 '^theorem unroll' <<<"$src")"
then pass "the candidate is not placed directly before the theorem inside the mutual block"
else failed "the candidate is not placed directly before the theorem inside the mutual block"; echo "$src"; fi
report
