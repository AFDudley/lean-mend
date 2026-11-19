#!/usr/bin/env bash
# tests/probe-gap.sh: a site after a use of syntax that the same file declares
# (docs/architecture.md § The probe, `node`). App/Gap.lean declares the tactic
# `gap_triv` and uses it before a `simpa` that dep v2 breaks. A parse with the
# environment of the imports only does not parse the command that uses
# `gap_triv`, so the `simpa` got no node and no candidate. EquiVM run 5
# stopped on this shape (Examples/VyperERC20/Allowance.lean, byte 22618), and
# run 7 left such sites as residue. The probe now reads the commands that the
# elaboration of the file parsed, with the file's own syntax.
#
# Checks: the probe's `node` command gives the `simpa` byte its `simpa` node,
# and `lean-mend run --adopt --rules` repairs the site with the simpa rule.
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
check "the probe gives byte $offset its simpa node, inside the theorem after the macro" \
  ".offset == $offset and (.nodes | map(.kind) | index(\"Lean.Parser.Tactic.simpa\") != null)
   and (.nodes | map(.kind) | index(\"Lean.Parser.Command.declaration\") != null)" "$reply"

# The whole run: the site gets its node, so the simpa rule proposes
# `simpaToExact`, and the run repairs App.Gap; App, which imports it, builds.
if out=$("$bin" run "$app" --adopt --rules "$fx/rules"); then
  pass "lean-mend run exits 0"
else
  failed "lean-mend run exits 0"
fi
echo "$out"
[ -n "$out" ] || out='{}'
check "the run is done with no residue" '.state == "done" and .residue == []' "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
check "App.Gap: one typeMismatch site, and lean-mend did not give up" \
  '(map(select(.obs == "diagnosed" and .detail.module == "App.Gap"))[0].detail.detail | map(.class))
     == ["LeanMend.ErrorClass.typeMismatch"]
   and (any(.[]; .obs == "gaveUp") | not)' "$ledger"
subjects=$(g log --format=%s main..lean-mend/mend)
if [ "$(grep -c '^lean-mend: simpa-mismatch: ' <<<"$subjects")" = 1 ] && [ "$(wc -l <<<"$subjects")" = 1 ]
then pass "the mend branch holds one commit, a candidate of simpa-mismatch"
else failed "the mend branch holds one commit, a candidate of simpa-mismatch"; echo "$subjects"; fi
if grep -q 'exact h' "$app/App/Gap.lean" && (cd "$app" && lake build -q >/dev/null)
then pass "the mended app has 'exact h' and builds"
else failed "the mended app has 'exact h' and builds"; cat "$app/App/Gap.lean"; fi
report
