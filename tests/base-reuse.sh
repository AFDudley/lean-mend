#!/usr/bin/env bash
# tests/base-reuse.sh: a second `lean-mend run --adopt` of the same bump reuses
# the baseline worktree and the stored baseline certificate (Shell/Driver.lean,
# baseTree and baseCertificate; law LM3), and reaches the same result as the
# first run. A baseline worktree with a changed tracked file is not reused.
# The fixture is tests/rename.sh's own: the app uses Dep.old, the bump moves dep
# from v1 to v3, and v2's deprecated alias records the rename.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/rename"
work="$root/.scratch/base-reuse"
tc="leanprover/lean4:v4.33.1"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fi
}

rm -rf "$work" && mkdir -p "$work"
cp -r "$fx/dep-v2" "$work/dep-v2" && echo "$tc" > "$work/dep-v2/lean-toolchain"
app="$work/app"
cp -r "$fx/app" "$app" && echo "$tc" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
cp -r "$fx/dep-v1" "$app/dep"
g() { git -C "$app" "$@"; }
g init -q -b main && g add -A && g commit -q -m "app on dep v1"
rm -rf "$app/dep" && cp -r "$fx/dep-v3" "$app/dep"
g add -A && g commit -q -m "bump dep to v3"

run() { "$bin" run "$app" --adopt --aliases-from "$work/dep-v2"; }
baseline() { jq -c 'select(.obs == "baseline") | .detail' "$app/.lean-mend/ledger.jsonl"; }
reset_mend() { g switch -q main && g branch -q -D lean-mend/mend; }

out1=$(run)
b1=$(baseline)
check "the first run adds the baseline worktree" '.worktreeReused == false' "$b1"
check "the first run computes the baseline certificate" '.certificateStored == false' "$b1"
n1=$(g rev-list --count main..lean-mend/mend)
olean=$(find "$app/.lean-mend/base/.lake/build/lib" -name 'Use.olean' | head -1)
mtime1=$(stat -c %Y "$olean")

reset_mend
out2=$(run)
b2=$(baseline)
check "the second run reuses the baseline worktree" '.worktreeReused == true' "$b2"
check "the second run reads the stored baseline certificate" '.certificateStored == true' "$b2"
[ "$(jq -c '{decls, failing}' <<<"$b1")" = "$(jq -c '{decls, failing}' <<<"$b2")" ] \
  && pass "both runs have the same baseline" || failed "both runs have the same baseline"
[ "$(jq -c '{state, residue}' <<<"$out1")" = "$(jq -c '{state, residue}' <<<"$out2")" ] \
  && pass "both runs end in the same state with the same residue" \
  || { failed "both runs end in the same state with the same residue"; echo "$out1"; echo "$out2"; }
n2=$(g rev-list --count main..lean-mend/mend)
[ "$n1" = "$n2" ] && pass "both runs make the same number of commits ($n1)" \
  || failed "both runs make the same number of commits ($n1, $n2)"
[ "$(stat -c %Y "$olean")" = "$mtime1" ] && pass "the reused baseline is not rebuilt" \
  || failed "the reused baseline is not rebuilt"

# A tracked file changed in the kept worktree: the run adds the worktree again.
reset_mend
echo '-- changed' >> "$app/.lean-mend/base/App/Use.lean"
run >/dev/null
check "a baseline worktree with a changed tracked file is added again" \
  '.worktreeReused == false' "$(baseline)"
report
