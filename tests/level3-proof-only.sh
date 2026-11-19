#!/usr/bin/env bash
# Level 3, a proof-only repair (docs/machine.md § Level 3, § Acceptance;
# docs/decisions.md D15), on tests/fixtures/level3-proof-only. `Dep.lem`'s
# proof goes classical at dep v2 (`Classical.choice`); `Dep.lemC` keeps the
# v1 constructive proof under a new name. `App.t` reaches `Dep.lem`
# directly, and `App.useT` reaches it through `App.t` — D14 makes
# `App.t` the one site for both findings. The fixture rule
# `proof-only-swap` replaces `Dep.lem` with `Dep.lemC` in `App.t`'s body.
# The run must go built -> repairing -> built -> done: one commit, no
# card, and `App.useT`'s finding closed by the walk (decision D15), with no
# rebuild of `App.Use` (the ledger's `repair` entry names the `"walk"`
# method).
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"

root="$_lm_root"
fx="$root/tests/fixtures/level3-proof-only"
work="$root/.scratch/level3-proof-only"
tc="leanprover/lean4:v4.33.1"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
dep="$work/dep"
mkdir -p "$dep"
d() { git -C "$dep" "$@"; }
cp -r "$fx/dep-v1/." "$dep/"
d init -q -b main && d add -A && d commit -q -m "dep v1"
v1=$(d rev-parse HEAD)
rm -rf "$dep/Dep" "$dep/Dep.lean" && cp -r "$fx/dep-v2/." "$dep/"
d add -A && d commit -q -m "dep v2"
v2=$(d rev-parse HEAD)

app="$work/app"
cp -r "$fx/app" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "$tc" > "$app/lean-toolchain"
printf 'name = "app"\ndefaultTargets = ["App"]\n\n[[require]]\nname = "dep"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "App"\n' \
  "$dep" "$v1" > "$app/lakefile.toml"
(cd "$app" && lake update >&2)
g init -q -b main && g add -A && g commit -q -m "app at v4.33.1, dep v1"
# the bump: the dep moves to v2, no change to the app's own source
sed -i "s/$v1/$v2/" "$app/lakefile.toml"
(cd "$app" && lake update >&2)
g add -A && g commit -q -m "bump dep to v2"

out=$("$bin" run "$app" --adopt --rules "$fx/rules")
echo "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")

check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}

check "the run ends done, with no residue" '.state == "done" and .residue == []' "$out"
check "the run entered repairing" \
  '[.[] | select(.obs == "certificate" and .state == "repairing")] | length == 1' "$ledger"
check "one repair commit, by proof-only-swap, closing both App.t and App.useT" \
  '[.[] | select(.obs == "repair" and .detail.accepted == true)] as $r
   | ($r | length) == 1 and ($r[0].detail.rule | test("proof-only-swap"))
     and ($r[0].detail.closes | sort) == ["App.t", "App.useT"]' "$ledger"
check "the acceptance used the walk, not a rebuild (decision D15)" \
  '[.[] | select(.obs == "repair" and .detail.accepted == true)][0].detail.detail.method == "walk"' \
  "$ledger"
check "the run left repairing for built, then reached done with no card" \
  '[.[] | select(.obs == "repaired")] | length == 1' "$ledger"

src=$(cat "$app/App/T.lean")
grep -q 'Dep.lemC' <<<"$src" && pass "App.t now calls Dep.lemC" || { failed "App.t text"; echo "$src"; fail=1; }
! grep -q 'Dep\.lem\b' <<<"$src" || grep -q 'Dep.lemC' <<<"$src" || { failed "App.t still names Dep.lem alone"; fail=1; }
n=$(git -C "$app" rev-list --count main..lean-mend/mend)
[ "$n" = 1 ] && pass "one commit on lean-mend/mend" || { failed "commits: $n"; fail=1; }
subjects=$(git -C "$app" log --format=%s main..lean-mend/mend)
grep -q '^lean-mend: proof-only-swap: ' <<<"$subjects" && pass "the commit names proof-only-swap" \
  || { failed "commit subject: $subjects"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && pass "the mended app builds" || { failed "build"; fail=1; }
[ -z "$("$bin" cards "$app")" ] && pass "no card is left" || { failed "cards: $("$bin" cards "$app")"; fail=1; }
# App.Use.lean's content never changed: no rebuild/commit touched it.
unchanged=$(diff -q "$fx/app/App/Use.lean" "$app/App/Use.lean" || true)
[ -z "$unchanged" ] && pass "App.Use.lean is unchanged: the walk needed no rebuild of it" \
  || { failed "App.Use.lean changed"; fail=1; }
report
