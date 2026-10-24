#!/usr/bin/env bash
# lean-mend run --adopt on tests/fixtures/rename: the app uses Dep.old; the bump
# moves dep from v1 (Dep.old) to v3 (Dep.new only); v2 is the release whose
# @[deprecated] alias records the rename. See docs/rules.md (derived rules).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/.lake/build/bin/lean-mend"
fx="$root/tests/fixtures/rename"
work="$root/.scratch/rename"
tc="leanprover/lean4:v4.33.1"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then echo "ok   $1"; else echo "FAIL $1"; echo "$3"; fail=1; fi
}

rm -rf "$work" && mkdir -p "$work"
cp -r "$fx/dep-v2" "$work/dep-v2" && echo "$tc" > "$work/dep-v2/lean-toolchain"
app="$work/app"
cp -r "$fx/app" "$app" && echo "$tc" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
cp -r "$fx/dep-v1" "$app/dep"
g() { git -C "$app" -c user.email=t@lean-mend -c user.name=t "$@"; }
g init -q -b main && g add -A && g commit -q -m "app on dep v1"
rm -rf "$app/dep" && cp -r "$fx/dep-v3" "$app/dep"
g add -A && g commit -q -m "bump dep to v3"

out=$(GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend \
  bash -c 'cd "$1" && "$2" run app --adopt --aliases-from dep-v2' _ "$work" "$bin")
echo "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
check "the run ends done with no residue" '.state == "done" and .residue == []' "$out"
check "the alias map holds the v2 rename" \
  'map(select(.obs == "bumped"))[0].detail.aliases | index("Dep.old → Dep.new") != null' "$ledger"
check "4 errors, 2 accepted patches, error count 4 → 1 → 0" \
  '(map(select(.obs == "diagnosed"))[0].detail.sites == 4) and ([.[] | select(.obs == "rebuilt") | .detail.errors] == [1, 0])' "$ledger"
check "sites carry their declaration and region" \
  'map(select(.obs == "diagnosed"))[0].detail.detail as $d
   | ($d | map(select(.decl == "App.three"))[0].region == "LeanMend.SiteRegion.body")
     and ($d | map(select(.decl == "App.old_id"))[0].region == "LeanMend.SiteRegion.statement")' "$ledger"
check "the statement that names Dep.old is unchanged after the alias map (no finding)" \
  'map(select(.obs == "certificate"))[0].state == "done"' "$ledger"
n=$(git -C "$app" rev-list --count main..lean-mend/mend)
[ "$n" = 2 ] && echo "ok   two commits on lean-mend/mend" || { echo "FAIL commits on lean-mend/mend: $n"; fail=1; }
grep -q 'Dep.new 3' "$app/App/Use.lean" && ! grep -q 'Dep.old' "$app/App/Use.lean" \
  && echo "ok   the source uses Dep.new only" || { echo "FAIL source"; cat "$app/App/Use.lean"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && echo "ok   the mended app builds" || { echo "FAIL build"; fail=1; }

# Without the v2 alias source no rule matches: every site is residue.
rm -rf "$app/.lean-mend" && g switch -q main && g branch -q -D lean-mend/mend
out=$(GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend \
  "$bin" run "$app" --adopt)
check "without the alias source: done, App.Use residue, App blocked behind it" \
  '.state == "done" and .residue == ["App.Use", "App"]' "$out"
n=$(git -C "$app" rev-list --count main..lean-mend/mend)
[ "$n" = 0 ] && echo "ok   no commit without an accepted patch" || { echo "FAIL commits: $n"; fail=1; }
exit $fail
