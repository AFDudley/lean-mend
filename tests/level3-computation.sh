#!/usr/bin/env bash
# Level 3, a computation-changing repair (docs/machine.md § Level 3, §
# Acceptance; docs/decisions.md D15), on tests/fixtures/level3-computation.
# `Dep.pick` routes through `Classical.propDecidable` at dep v2, so it
# depends on `Classical.choice`. `Dep.pickC` keeps the v1 computable value
# under a new name. `App.g` reaches `Dep.pick` directly, and `App.useG`
# reaches it through `App.g` — D14 makes `App.g` the one site for both
# findings. The fixture rule `computation-swap` replaces `Dep.pick` with
# `Dep.pickC` in `App.g`'s body. `App.g` is a `def`, not a `theorem`, so
# its edit can change what it computes (decision D16): acceptance needs
# condition 1's rebuild path, not the walk, and must rebuild `App.Use`
# too — "the importers that use a changed declaration" (decision D15).
# The run must go built -> repairing -> built -> awaiting: one commit, the
# axiom violation closed, and the ledger's `repair` entry names the
# `"rebuild"` method with `App.Use` among the rebuilt modules. `App.g`'s
# own definition changed by the edit (decision D16), so one Behavior card
# stays open for a person: the computation path repairs the axiom finding
# but does not auto-close the definition-change finding it leaves behind.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"

root="$_lm_root"
fx="$root/tests/fixtures/level3-computation"
work="$root/.scratch/level3-computation"
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

check "the run ends awaiting, with one Behavior card on App.g left for a person" \
  '.state == "awaiting" and .residue == []
   and (.findings | length) == 1
   and .findings[0].decl == "App.g" and (.findings[0].reason | test("definitionChanged"))' "$out"
check "the run entered repairing" \
  '[.[] | select(.obs == "certificate" and .state == "repairing")] | length == 1' "$ledger"
check "one repair commit, by computation-swap, closing both App.g and App.useG" \
  '[.[] | select(.obs == "repair" and .detail.accepted == true)] as $r
   | ($r | length) == 1 and ($r[0].detail.rule | test("computation-swap"))
     and ($r[0].detail.closes | sort) == ["App.g", "App.useG"]' "$ledger"
check "the acceptance used the rebuild, not the walk (decision D15)" \
  '[.[] | select(.obs == "repair" and .detail.accepted == true)][0].detail.detail.method == "rebuild"' \
  "$ledger"
check "the rebuild covered App.Use (the importer that uses App.g)" \
  '[.[] | select(.obs == "repair" and .detail.accepted == true)][0].detail.detail.rebuiltModules == ["App.Use"]' \
  "$ledger"
check "the run left repairing for built, then reached awaiting with the one card" \
  '[.[] | select(.obs == "repaired")] | length == 1' "$ledger"

src=$(cat "$app/App/G.lean")
grep -q 'Dep.pickC' <<<"$src" && pass "App.g now calls Dep.pickC" || { failed "App.g text"; echo "$src"; fail=1; }
! grep -q 'Dep\.pick\b' <<<"$src" || grep -q 'Dep.pickC' <<<"$src" || { failed "App.g still names Dep.pick alone"; fail=1; }
n=$(git -C "$app" rev-list --count main..lean-mend/mend)
[ "$n" = 1 ] && pass "one commit on lean-mend/mend" || { failed "commits: $n"; fail=1; }
subjects=$(git -C "$app" log --format=%s main..lean-mend/mend)
grep -q '^lean-mend: computation-swap: ' <<<"$subjects" && pass "the commit names computation-swap" \
  || { failed "commit subject: $subjects"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && pass "the mended app builds" || { failed "build"; fail=1; }
cards=$("$bin" cards "$app")
n_cards=$(wc -l <<<"$cards")
[ "$n_cards" = 1 ] && grep -q 'behavior App.g' <<<"$cards" \
  && pass "exactly one card, a Behavior card on App.g" \
  || { failed "cards: $cards"; fail=1; }
# App.Use.lean's text never changed: it was rebuilt, not edited.
unchanged=$(diff -q "$fx/app/App/Use.lean" "$app/App/Use.lean" || true)
[ -z "$unchanged" ] && pass "App.Use.lean's text is unchanged: it was rebuilt, not edited" \
  || { failed "App.Use.lean changed"; fail=1; }
report
