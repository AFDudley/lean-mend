#!/usr/bin/env bash
# tests/cert-unread.sh: a declaration that the certificate selects but whose
# row the probe cannot give stops the run with the typed error DeclUnread
# (docs/verification.md § The certificate). It is never left out in silence.
#
# tests/fixtures/cert-unread/app is an app at Lean v4.29.0. Its module App.T
# declares a macro command that expands to a `local notation`, and the
# statement of the theorem `App.local_sum` uses that notation. The probe does
# not elaborate the macro command (`scopeKinds` in probe/Probe.lean), so the
# statement does not parse in the probe. The bump commit only sets v4.33.1.
# The baseline certificate is the first one taken: the run must stop there,
# exit 3, print `halted declUnread` with the module and the declaration, and
# record the stop in the ledger.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/cert-unread"
work="$root/.scratch/cert-unread"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$fx/app" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
git -C "$app" commit -qam "bump to v4.33.1"

code=0
out=$("$bin" run "$app" --adopt) || code=$?
echo "$out" >&2
[ -n "$out" ] || out='{}'
if [ "$code" -eq 3 ] && jq -e '.state == "halted declUnread" and .module == "App.T" and
    .decl == "App.local_sum" and (.reason | length > 0)' <<<"$out" >/dev/null
then pass "the run stops with declUnread, exit 3, naming App.T and App.local_sum"
else failed "the run stops with declUnread, exit 3, naming App.T and App.local_sum"; fi
if jq -se '[.[] | select(.obs == "declUnread" and .detail.decl == "App.local_sum")] | length == 1' \
    "$app/.lean-mend/ledger.jsonl" >/dev/null
then pass "the ledger records the declUnread stop once"
else failed "the ledger records the declUnread stop once"; fi
report
