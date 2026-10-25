#!/usr/bin/env bash
# tests/order.sh <fixture>: S1a (docs/parallel.md X1, X2, X6). Breaks two
# declarations of one module at once, so both error sites are open together,
# then checks the ledger: the first give-up is at the source-earliest
# declaration, not at whichever one the shell reports first.
#
# stdout carries one JSON object and nothing else:
# {"first_attempt_is_source_earliest": true|false}.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/.lake/build/bin/lean-mend"
fx="${1:?usage: tests/order.sh <fixture>}"
work="$root/.scratch/order"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work"
mkdir -p "$work"
app="$work/app"
cp -r "$fx/." "$app/"
cat "$root/lean-toolchain" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
git -C "$app" init -q -b main
git -C "$app" add -A
git -C "$app" commit -q -m "app builds"

# Break earlyVal and lateVal in one commit, so the module opens with two
# error sites at once: the source-earliest at line 4, the other at line 6.
sed -i 's/1 + 1/unknownEarlyIdent/; s/2 + 2/unknownLateIdent/' "$app/App.lean"
git -C "$app" add -A
git -C "$app" commit -q -m "break earlyVal and lateVal at once"
earlyLine=$(grep -n 'def earlyVal' "$app/App.lean" | head -1 | cut -d: -f1)

"$bin" run "$app" --adopt >/dev/null

firstGaveUpLine=$(jq -s -c '[.[] | select(.obs == "gaveUp")][0].detail.line' "$app/.lean-mend/ledger.jsonl")

if [ "$firstGaveUpLine" = "$earlyLine" ]; then earliest=true; else earliest=false; fi
jq -nc --argjson v "$earliest" '{first_attempt_is_source_earliest: $v}'
[ "$earliest" = true ]
