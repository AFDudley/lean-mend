#!/usr/bin/env bash
# tests/statement-change.sh FIXTURE EXPECT: the certificate compares a
# statement as its token sequence (docs/verification.md § The certificate).
# FIXTURE/app is an app at Lean v4.29.0. The bump commit sets v4.33.1 and
# copies FIXTURE/head over the app, which changes one theorem's statement.
# Nothing fails to build, so `lean-mend run --adopt` goes to the certificate
# at once.
#
# EXPECT `done`: the statement differs only in layout (tests/fixtures/
# statement-layout), and the run ends done with no finding. Before the
# token comparison, EquiVM run 7 halted on this shape.
# EXPECT `invariantBroken`: the statement differs in one token
# (tests/fixtures/statement-token), and the run halts with invariantBroken
# at the theorem's module. The same holds for a statement that parses only
# with the file's own scopes or syntax: inside `open` of a scoped notation
# (statement-scoped), with a `local notation` of the file
# (statement-notation), and with an identifier that another module of the
# probe's batch makes a token (statement-batch-token). The probe's old
# parse, of each declaration alone with the batch's imports and no scope,
# gave no row for these theorems, and their token change was no finding.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$(cd "$1" && pwd)"
expect=$2
work="$root/.scratch/statement-change-$(basename "$fx")"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$fx/app" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
cp -r "$fx/head/." "$app/"
git -C "$app" add -A && git -C "$app" commit -q -m "bump to v4.33.1; edit a statement"

out=$("$bin" run "$app" --adopt) || true
echo "$out"
[ -n "$out" ] || out='{}'
case "$expect" in
  done)
    if jq -e '.state == "done" and .residue == [] and ((.findings // []) == [])' <<<"$out" >/dev/null
    then pass "a statement that differs only in layout: the run is done with no finding"
    else failed "a statement that differs only in layout: the run is done with no finding"; fi ;;
  invariantBroken)
    if jq -e '.state == "halted LeanMend.Refusal.invariantBroken \"App.T\""' <<<"$out" >/dev/null
    then pass "a statement that differs in one token: the run halts with invariantBroken at App.T"
    else failed "a statement that differs in one token: the run halts with invariantBroken at App.T"; fi ;;
  *) failed "EXPECT is done or invariantBroken, not '$expect'" ;;
esac
report
