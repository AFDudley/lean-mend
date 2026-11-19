#!/usr/bin/env bash
# A Behavior finding whose body change is in proofs only is accepted at
# once, with no card (docs/decisions.md D16; docs/static-diff.md § 6,
# decision S6), on tests/fixtures/card-body. The app is committed at Lean
# v4.29.0 (v1/), then bumped to v4.33.1 in a commit that also edits
# App/Hand.lean by hand (v2/), as the bump commit of EquiVM run 10 held the
# repairs of run 9. The run repairs App.checked with the rule
# simpa-close-transparency, inside a proof. The bump commit changes a proof
# of App.sized and the number that App.count computes.
#
# App.checked and App.sized change in proofs only, so both auto-accept: no
# card, and the ledger holds `lean-mend`'s own judgment. App.count changes
# the number a `by` block computes, outside a proof, so it still gets a
# card, and the card states that the proof-only check failed and why.
#
# The Trace of a card lists the commits that changed the body from the
# baseline commit on. Before this rule, Trace listed only the commits after
# the bump commit that touch the module, so the card of App.sized listed
# nothing, as card c-1 of run 10.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/card-body"
work="$root/.scratch/card-body"
rule=simpa-close-transparency
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work/rules"
cp "$root/rules/proposed/$rule.json" "$work/rules/"
app="$work/app"
cp -r "$fx/v1" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0"
cp -r "$fx/v2/." "$app/"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
g add -A && g commit -q -m "bump to v4.33.1, with a hand repair"
bump=$(g rev-parse HEAD)

out=$("$bin" run "$app" --adopt --rules "$work/rules")
echo "$out"
cards="$app/.lean-mend/cards"
ledger="$app/.lean-mend/ledger.jsonl"
session="$app/.lean-mend/session.json"
card() { grep -l -F "**Subject.** \`$1\`" "$cards"/c-*.md 2>/dev/null || true; }
has() {  # has <description> <file> <fixed string>…
  local desc=$1 file=$2; shift 2
  local s
  for s in "$@"; do
    if ! grep -q -F -- "$s" "$file"; then failed "$desc"; echo "missing: $s"; cat "$file"; fail=1; return; fi
  done
  pass "$desc"
}

if jq -e '.state == "awaiting" and ([.findings[] | select(.reason == "LeanMend.Reason.definitionChanged") | .decl] | sort) == ["App.count"]' <<<"$out" >/dev/null
then pass "App.checked and App.sized auto-accept; only App.count still waits on a Behavior card"
else failed "one Behavior card, App.count"; fail=1; fi
[ "$(g rev-list --count "$bump"..lean-mend/mend)" = 1 ] && pass "one commit on lean-mend/mend" \
  || { failed "one commit on lean-mend/mend"; fail=1; }

for d in App.checked App.sized; do
  if [ -z "$(card "$d")" ]
  then pass "$d: no card, the proof-only change auto-accepted"
  else failed "$d: no card, the proof-only change auto-accepted"; fail=1; fi
  if jq -e --arg d "$d" '[inputs | select(.obs == "judgment" and .detail.subject == $d and .detail.answer == "accept")] | length == 1' \
      "$ledger" >/dev/null
  then pass "$d: the ledger holds lean-mend's own accept judgment"
  else failed "$d: the ledger holds lean-mend's own accept judgment"; cat "$ledger"; fail=1; fi
done
if jq -e '.evidence.bodies | map(.decl) | sort == ["App.checked", "App.count", "App.sized"]' "$session" >/dev/null
then pass "session.json keeps the body evidence of all three declarations, cards or not"
else failed "session.json body evidence"; cat "$session"; fail=1; fi

count=$(card App.count)
has "App.count: a change of the number that a by block computes is not in proofs only" "$count" \
  "The change is not in proofs only" '-:= by exact 2' '+:= by exact 3'
report
