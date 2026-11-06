#!/usr/bin/env bash
# tests/dataflow.sh: dataflow scheduling across modules (docs/parallel.md
# § Level 2, P8, P10-P13, P21-P23). tests/fixtures/dataflow breaks three
# modules in one commit. Slow and Fast do not import each other. Dep imports
# Fast only. Clean imports Fast and has no break of its own, so it is blocked
# until Fast builds. Each accepted fix of Slow makes the kernel decide a
# plain recursive count, so Slow's two attempts take several seconds each.
#
# Checks, from the run's ledger and its mend branch:
# - Dep's first attempt starts before Slow's last attempt ends: Dep does not
#   wait for the unrelated module Slow.
# - The commits on lean-mend/mend touch the modules in the canonical
#   (topological) order that the run's first `build` line lists, not in
#   completion order. The canonical order is checked against the fixture's
#   imports: Fast comes before Dep and Clean.
# - The "diagnosed" lines name the modules in the same canonical order.
# - The branch tree equals the expected tree. The expected tree is `main`'s
#   tree with Slow.lean, Fast.lean and Dep.lean replaced by the hand-written
#   files in tests/fixtures/dataflow/expected: each is the broken file with
#   its one rule's replacement applied by hand. Clean.lean does not change.
# - Clean, blocked at HEAD, gets one "moduleBuild" line with status built.
# - The run ends with no residue, and the main checkout has no uncommitted
#   change: the commits through the git index match the files on disk.
#
# stdout carries one JSON object and nothing else (tests/lib/report.sh).
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/dataflow"
work="$root/.scratch/dataflow"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work"
mkdir -p "$work"
app="$work/app"
mkdir -p "$app"
cp "$fx/lakefile.toml" "$app/lakefile.toml"
cat "$root/lean-toolchain" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
printf 'theorem fooS1 : True := by trivial\n\ntheorem fooS2 : True := by trivial\n' > "$app/Slow.lean"
printf 'def fastVal : Nat := 1\n\ntheorem fooF : True := by trivial\n' > "$app/Fast.lean"
printf 'import Fast\n\ntheorem fooD : fastVal = 1 := by rfl\n' > "$app/Dep.lean"
printf 'import Fast\n\ntheorem fooC : fastVal = 1 := rfl\n' > "$app/Clean.lean"
g() { git -C "$app" "$@"; }
g init -q -b main && g add -A && g commit -q -m "app builds"

# Break Slow, Fast and Dep in one commit. Dep and Clean are blocked at HEAD,
# because Fast fails.
cp "$fx/Slow.lean" "$fx/Fast.lean" "$fx/Dep.lean" "$app/"
g add -A && g commit -q -m "break Slow, Fast and Dep"

t0=$(date +%s)
# A limit of 64 GiB admits every module probe at once (docs/parallel.md P24),
# whatever memory the host has free.
out=$("$bin" run "$app" --adopt --rules "$fx/rules" --max-memory 64)
t1=$(date +%s)
echo "$out"
ledger="$app/.lean-mend/ledger.jsonl"

if jq -e '.residue == [] and (.state == "done" or .state == "awaiting")' <<<"$out" >/dev/null; then
  pass "the run ends with no residue"
else failed "the run ends with no residue"; fi

# The canonical order: the module order of the first "build" line, which
# lists every module of the run in the driver's topological order.
canonical=$(jq -sc '[.[] | select(.obs == "build")][0].detail | map(split(": ")[0])' "$ledger")
echo "canonical order: $canonical"
if jq -e 'index("Fast") < index("Dep") and index("Fast") < index("Clean") and index("Slow") < index("Dep")' \
    <<<"$canonical" >/dev/null; then
  pass "the canonical order is topological"
else failed "the canonical order is topological"; fi
mended=$(jq -c 'map(select(. == "Slow" or . == "Fast" or . == "Dep"))' <<<"$canonical")

attempts=$(jq -sc '[.[] | select(.obs == "moduleAttempt") | .detail]' "$ledger")
depFirstStart=$(jq '[.[] | select(.module == "Dep") | .startedAt] | min' <<<"$attempts")
slowEnd=$(jq '[.[] | select(.module == "Slow") | .finishedAt] | max' <<<"$attempts")
fastEnd=$(jq '[.[] | select(.module == "Fast") | .finishedAt] | max' <<<"$attempts")
slowStart=$(jq '[.[] | select(.module == "Slow") | .startedAt] | min' <<<"$attempts")
echo "Slow attempts: $slowStart..$slowEnd ms; Fast ends at $fastEnd ms; Dep's first attempt starts at $depFirstStart ms"
if [ "$depFirstStart" != null ] && [ "$slowEnd" != null ] && [ "$depFirstStart" -lt "$slowEnd" ]; then
  pass "Dep's first attempt starts before Slow's mend ends"
else failed "Dep's first attempt starts before Slow's mend ends"; fi

# The module of each mend-branch commit: the one file it touches, without
# its ".lean" suffix. Each module has commits in one run, so the run of
# equal neighbours is collapsed to one entry.
commitOrder=$(g log --name-only --format= --reverse main..lean-mend/mend | grep -v '^$' |
  sed 's/\.lean$//' | uniq | jq -R . | jq -sc .)
echo "commit order: $commitOrder"
if [ "$commitOrder" = "$mended" ]; then pass "the commits follow the canonical order"
else failed "the commits follow the canonical order"; fi

diagnosedOrder=$(jq -sc '[.[] | select(.obs == "diagnosed") | .detail.module]' "$ledger")
if [ "$diagnosedOrder" = "$mended" ]; then pass "the ledger replays the modules in the canonical order"
else failed "the ledger replays the modules in the canonical order"; fi

idx="$work/expected.index"
GIT_INDEX_FILE="$idx" git -C "$app" read-tree main
for f in Slow.lean Fast.lean Dep.lean; do
  sha=$(git -C "$app" hash-object -w "$fx/expected/$f")
  GIT_INDEX_FILE="$idx" git -C "$app" update-index --cacheinfo "100644,$sha,$f"
done
expectedTree=$(GIT_INDEX_FILE="$idx" git -C "$app" write-tree)
branchTree=$(g rev-parse 'lean-mend/mend^{tree}')
if [ "$expectedTree" = "$branchTree" ]; then pass "the branch tree equals the expected tree"
else failed "the branch tree equals the expected tree"; g diff "$expectedTree" "$branchTree" >&2 || true; fi

if jq -se '[.[] | select(.obs == "moduleBuild" and .detail.module == "Clean") | .detail.status]
    == ["LeanMend.ModStatus.built"]' "$ledger" >/dev/null; then
  pass "Clean builds once Fast builds"
else failed "Clean builds once Fast builds"; fi

if [ -z "$(g status --porcelain --untracked-files=no)" ]; then pass "the main checkout has no uncommitted change"
else failed "the main checkout has no uncommitted change"; g status --porcelain >&2; fi

echo "wall time of the run: $((t1 - t0)) s"
report
