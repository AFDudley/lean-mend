#!/usr/bin/env bash
# tests/expose.sh <fixture>: S1b (docs/parallel.md X3, X4, X5). The fixture's
# App.lean breaks one declaration with one head error. The fixture's rules/
# directory holds the one rule that fixes it. The edit either exposes later
# errors in the same declaration at a smaller byte reach than the old head
# (the Core accepts it, tests/fixtures/expose-two) or leaves an error at a
# byte reach larger than the old head, a position earlier in the declaration
# (the Core rejects it, tests/fixtures/expose-back).
#
# stdout carries one JSON object and nothing else: {"verdict": "accepted" |
# "rejected"}, decided by whether lean-mend committed the fixture's rule on
# the mend branch.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="${1:?usage: tests/expose.sh <fixture>}"
work="$root/.scratch/expose"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work"
mkdir -p "$work"
app="$work/app"
mkdir -p "$app"
cp "$fx/lakefile.toml" "$app/lakefile.toml"
cat "$root/lean-toolchain" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
cat > "$app/App.lean" << 'EOF'
theorem placeholder : True := by trivial
EOF
git -C "$app" init -q -b main
git -C "$app" add -A
git -C "$app" commit -q -m "app builds"
cp "$fx/App.lean" "$app/App.lean"
git -C "$app" add -A
git -C "$app" commit -q -m "break foo"

"$bin" run "$app" --adopt --rules "$fx/rules" >&2

n=$(git -C "$app" rev-list --count main..lean-mend/mend)
if [ "$n" -gt 0 ]; then verdict=accepted; else verdict=rejected; fi
jq -nc --arg v "$verdict" '{verdict: $v}'
