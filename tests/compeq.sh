#!/usr/bin/env bash
# tests/compeq.sh: computational equality (`docs/static-diff.md` § 4,
# slice 5), on tests/fixtures/compeq. Two Behavior findings whose source
# bytes change outside any proof (decision D16's own proof-only check
# gives no auto-accept), but whose elaborated, proof-erased term is
# identical: `App.renamed` (an internal `let`-bound variable renamed) and
# `App.usesTrust` (the same rename, through an `@[extern]` constant,
# `App.myAdd`, a stated trust point, decision S4). `certifyEqual`
# (`LeanMend.Core.CompEq`) certifies both equal; `autoAcceptCompEq`
# (`LeanMend.Shell.Driver`) auto-accepts both, with no card, the same
# pattern decision D16's own proof-only check already follows.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/compeq"
work="$root/.scratch/compeq"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$fx/v1" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0"
cp -r "$fx/v2/." "$app/"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
g add -A && g commit -q -m "bump to v4.33.1, rename two local variables"

out=$("$bin" run "$app" --adopt)
echo "$out"
ledger="$app/.lean-mend/ledger.jsonl"
session="$app/.lean-mend/session.json"
cards="$app/.lean-mend/cards"

if jq -e '.state == "done"' <<<"$out" >/dev/null
then pass "the run ends done: both renames certify computationally equal"
else failed "the run ends done"; fail=1; fi

if [ ! -d "$cards" ] || [ -z "$(find "$cards" -maxdepth 1 -name 'c-*.md' 2>/dev/null)" ]
then pass "no card is written for App.renamed or App.usesTrust"
else failed "no card is written"; ls "$cards"; fail=1; fi

for subj in App.renamed App.usesTrust; do
  if jq -e --arg s "$subj" \
      '[inputs | select(.obs == "judgment" and .detail.subject == $s and .detail.answer == "accept" and .detail.author == "lean-mend: computational equality check")] | length == 1' \
      "$ledger" >/dev/null
  then pass "$subj: the ledger holds lean-mend's own computational-equality accept judgment"
  else failed "$subj: ledger judgment"; cat "$ledger"; fail=1; fi

  if jq -e --arg s "$subj" \
      '[inputs | select(.obs == "compEq" and .detail.subject == $s and .detail.result == "certified")] | length == 1' \
      "$ledger" >/dev/null
  then pass "$subj: the ledger holds a certified compEq note"
  else failed "$subj: compEq ledger note"; cat "$ledger"; fail=1; fi
done

if jq -e \
    '[inputs | select(.obs == "compEq" and .detail.subject == "App.usesTrust")][0].detail.trustPoints
     | map(select(.name == "App.myAdd" and .kind == "extern")) | length == 1' \
    "$ledger" >/dev/null
then pass "App.usesTrust: App.myAdd is listed as an extern trust point"
else failed "App.myAdd trust point"; cat "$ledger"; fail=1; fi

if jq -e '.cards == [] and (.evidence.bodies | map(.decl) | sort) == ["App.renamed", "App.usesTrust"]' \
    "$session" >/dev/null
then pass "session.json keeps the body evidence of both declarations, with no card"
else failed "session.json evidence"; cat "$session"; fail=1; fi

report
