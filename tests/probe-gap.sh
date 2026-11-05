#!/usr/bin/env bash
# tests/probe-gap.sh: a site that no parsed command contains
# (docs/architecture.md § The probe, `node`). App/Gap.lean declares the
# tactic `gap_triv` and uses it before a `simpa` that dep v2 breaks. The probe
# parses with the environment of the imports only, so the command that uses
# `gap_triv` does not parse, and the parser skips the bytes of the `simpa`.
# EquiVM run 5 stopped on this shape (Examples/VyperERC20/Allowance.lean,
# byte 22618): the probe threw "no command contains byte", and the second
# wait for the reaped probe process threw ECHILD.
#
# Checks: the probe gives the offset an empty node list and exits 0, and
# `lean-mend run --adopt --rules` ends with App.Gap as residue.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/probe-gap"
work="$root/.scratch/probe-gap"
tc="leanprover/lean4:v4.33.1"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$fx/app" "$app" && echo "$tc" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
cp -r "$fx/dep-v1" "$app/dep"
g() { git -C "$app" "$@"; }
g init -q -b main && g add -A && g commit -q -m "app on dep v1"
rm -rf "$app/dep" && cp -r "$fx/dep-v2" "$app/dep"
g add -A && g commit -q -m "bump dep to v2"

# The probe's `node` command at the byte of the proof's `simpa`, under dep v2.
(cd "$app" && lake build -q Dep >/dev/null)
cp "$root/probe/Probe.lean" "$work/Probe.lean"
offset=$(grep -bo 'simpa using' "$app/App/Gap.lean" | cut -d: -f1)
if reply=$(cd "$app" && lake env lean --run "$work/Probe.lean" node App/Gap.lean "$offset"); then
  pass "the probe's node command exits 0 at byte $offset"
else
  failed "the probe's node command exits 0 at byte $offset"
  reply='{}'
fi
check "the probe gives byte $offset an empty node list" ".offset == $offset and .nodes == []" "$reply"

# The whole run: the site gets no node, so the simpa rule proposes no
# candidate. App.Gap is residue, and App, which imports it, is residue too.
if out=$("$bin" run "$app" --adopt --rules "$fx/rules"); then
  pass "lean-mend run exits 0"
else
  failed "lean-mend run exits 0"
fi
echo "$out"
[ -n "$out" ] || out='{}'
check "the run is done, with App.Gap and App as residue" \
  '.state == "done" and (.residue | sort) == ["App", "App.Gap"]' "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
check "App.Gap: one typeMismatch site, and lean-mend gave up on it" \
  '(map(select(.obs == "diagnosed" and .detail.module == "App.Gap"))[0].detail.detail | map(.class))
     == ["LeanMend.ErrorClass.typeMismatch"]
   and any(.[]; .obs == "gaveUp")' "$ledger"
report
