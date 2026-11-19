#!/usr/bin/env bash
# A Behavior finding whose body change is in proofs only ends the run
# `done`, with no card (docs/decisions.md D16; docs/static-diff.md § 6,
# decision S6). The app has one declaration, `App.checked`
# (tests/fixtures/card-body's `App/Close.lean`, reused here): the rule
# `simpa-close-transparency` repairs it inside a proof. Nothing else in the
# app changes, so this is the one open finding of the run, and its
# auto-accept closes the run with no judgment from a person.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/card-body"
work="$root/.scratch/proof-only-accept"
rule=simpa-close-transparency
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work/rules" "$work/app/App"
cp "$root/rules/proposed/$rule.json" "$work/rules/"
app="$work/app"
cp "$fx/v1/lakefile.toml" "$app/lakefile.toml"
cp "$fx/v1/App/Close.lean" "$app/App/Close.lean"
printf 'import App.Close\n' > "$app/App.lean"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
g add -A && g commit -q -m "bump to v4.33.1"

out=$("$bin" run "$app" --adopt --rules "$work/rules")
echo "$out"
ledger="$app/.lean-mend/ledger.jsonl"
session="$app/.lean-mend/session.json"
cards="$app/.lean-mend/cards"

if jq -e '.state == "done"' <<<"$out" >/dev/null
then pass "the run ends done: the proof-only change needs no person's judgment"
else failed "the run ends done"; fail=1; fi

if [ ! -d "$cards" ] || [ -z "$(find "$cards" -maxdepth 1 -name 'c-*.md' 2>/dev/null)" ]
then pass "no card is written for App.checked"
else failed "no card is written for App.checked"; ls "$cards"; fail=1; fi

if jq -e '[inputs | select(.obs == "judgment" and .detail.subject == "App.checked" and .detail.answer == "accept")] | length == 1' \
    "$ledger" >/dev/null
then pass "the ledger holds lean-mend's own accept judgment for App.checked"
else failed "ledger judgment for App.checked"; cat "$ledger"; fail=1; fi

if jq -e '.cards == [] and (.evidence.bodies | map(.decl)) == ["App.checked"]' "$session" >/dev/null
then pass "session.json keeps the body evidence of App.checked, with no card"
else failed "session.json evidence for App.checked"; cat "$session"; fail=1; fi
report
