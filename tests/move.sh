#!/usr/bin/env bash
# A namespace move with no aliases (tests/fixtures/move): renamePrefix renames
# every occurrence in one edit, including a declaration the app declares under
# the moved prefix, and the run must end done, not invariantBroken.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/.lake/build/bin/lean-mend"
fx="$root/tests/fixtures/move"
work="$root/.scratch/move"
tc="leanprover/lean4:v4.33.1"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then echo "ok   $1"; else echo "FAIL $1"; echo "$3"; fail=1; fi
}
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$fx/app" "$app" && echo "$tc" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
cp -r "$fx/dep-v1" "$app/dep" && echo "$tc" > "$app/dep/lean-toolchain"
g() { git -C "$app" "$@"; }
g init -q -b main && g add -A && g commit -q -m "app on dep v1"
rm -rf "$app/dep" && cp -r "$fx/dep-v2" "$app/dep" && echo "$tc" > "$app/dep/lean-toolchain"
g add -A && g commit -q -m "bump dep to v2"

out=$("$bin" run "$app" --adopt --rules "$fx/rules" || true)
check "the run ends done: the declaration renamed by the move is found, not missing" \
  '.state == "done" and .residue == []' "$out"
! grep -q 'Old\.Map' "$app/App/Use.lean" && grep -q 'def New.Map.double' "$app/App/Use.lean" \
  && echo "ok   every Old.Map name moved, the declared one included" || { echo "FAIL source"; cat "$app/App/Use.lean"; fail=1; }
n=$(g rev-list --count main..lean-mend/mend)
[ "$n" = 1 ] && echo "ok   one commit: the move is one edit" || { echo "FAIL commits: $n"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && echo "ok   the mended app builds" || { echo "FAIL build"; fail=1; }
exit $fail
