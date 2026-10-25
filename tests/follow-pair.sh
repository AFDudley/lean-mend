#!/usr/bin/env bash
# tests/follow-pair.sh <fixture>: S1c (docs/parallel.md X7, § The D12
# combined candidate). The fixture's App/Pre.lean has one declaration whose
# statement and whose body both carry the valCompare pattern. With
# --follow-definition-changes, the body edit and the statement follow it
# needs go out as one candidate, so the Core tries both in one rebuild.
#
# stdout carries one JSON object and nothing else: {"attempts": N, "ok":
# true|false}. "attempts" counts the ledger's "rebuilt" observations for
# the run. "ok" is true when the run made exactly one such attempt, that
# attempt's commit changed both the statement line and the body line, and
# the Core accepted it (one commit on the mend branch).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="${1:?usage: tests/follow-pair.sh <fixture>}"
work="$root/.scratch/follow-pair"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work"
mkdir -p "$work"
app="$work/app"
mkdir -p "$app"
cp -r "$fx/App" "$fx/App.lean" "$fx/lakefile.toml" "$app/"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
git -C "$app" init -q -b main
git -C "$app" add -A
git -C "$app" commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
git -C "$app" add -A
git -C "$app" commit -q -m "bump to v4.33.1"

"$bin" run "$app" --adopt --rules "$fx/rules" --follow-definition-changes >&2

ledger="$app/.lean-mend/ledger.jsonl"
attempts=$(jq -s '[.[] | select(.obs == "rebuilt")] | length' "$ledger")
commits=$(git -C "$app" rev-list --count main..lean-mend/mend)
diff=""
if [ "$commits" -eq 1 ]; then
  diff=$(git -C "$app" show --format= lean-mend/mend)
fi
bothEdited=false
if grep -q '^+.*0 ≤ (match p.val with' <<<"$diff" && grep -q '^+.*match p.val with$' <<<"$diff"; then
  bothEdited=true
fi

ok=false
if [ "$attempts" -eq 1 ] && [ "$commits" -eq 1 ] && [ "$bothEdited" = true ]; then
  ok=true
fi
jq -nc --argjson a "$attempts" --argjson o "$ok" '{attempts: $a, ok: $o}'
[ "$ok" = true ]
