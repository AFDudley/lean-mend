#!/usr/bin/env bash
# tests/fleet.sh <fixture>: S3b (docs/parallel.md P8, P10-P12). The fixture
# breaks two independent modules, ModA and ModB, in one commit, so both
# start their mends at once. ModA's accepted fix makes the kernel decide a
# plain recursive count, so its attempt takes noticeably longer than ModB's:
# the run must still replay the two modules in the ledger, and commit them
# on the mend branch, in their canonical (topological) order — whichever
# module's worktree finishes first.
#
# stdout carries one JSON object and nothing else: {"max_concurrent_attempts",
# "attempts_sharing_a_worktree", "mend_branch_writers_other_than_driver",
# "commits_in_topological_order", "ledger_matches_sequential_order",
# "failed", "ok"}.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="${1:?usage: tests/fleet.sh <fixture>}"
work="$root/.scratch/fleet"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work"
mkdir -p "$work"
app="$work/app"
mkdir -p "$app"
cp "$fx/lakefile.toml" "$app/lakefile.toml"
cat "$root/lean-toolchain" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
cat > "$app/ModA.lean" << 'EOF'
theorem fooA : True := by trivial
EOF
cat > "$app/ModB.lean" << 'EOF'
theorem fooB : True := by trivial
EOF
git -C "$app" init -q -b main
git -C "$app" add -A
git -C "$app" commit -q -m "app builds"

# Break ModA and ModB in one commit, so both open at once: neither module
# imports the other, so both mends start at once.
cp "$fx/ModA.lean" "$app/ModA.lean"
cp "$fx/ModB.lean" "$app/ModB.lean"
git -C "$app" add -A
git -C "$app" commit -q -m "break ModA and ModB at once"

# A limit of 64 GiB admits both module probes at once (docs/parallel.md P24),
# whatever memory the host has free.
"$bin" run "$app" --adopt --rules "$fx/rules" --max-memory 64 >&2 || true

ledger="$app/.lean-mend/ledger.jsonl"

# canonicalOrder: the modules of the first "build" line, which lists every
# module of the run in the driver's canonical (topological) order — the
# order every check below is measured against.
canonicalOrder=$(jq -sc '[.[] | select(.obs == "build")][0].detail | map(split(": ")[0])' "$ledger")

# diagnosedOrder: the modules named by "diagnosed" lines, in ledger
# (replay) order — the order a one-module-at-a-time run would write them
# in, since each module's "diagnosed" line is the first thing its replay
# writes.
diagnosedOrder=$(jq -sc '[.[] | select(.obs == "diagnosed") | .detail.module]' "$ledger")
if [ "$canonicalOrder" = "$diagnosedOrder" ]; then ledgerMatchesSequentialOrder=true
else ledgerMatchesSequentialOrder=false
fi

# attempts: every "moduleAttempt" line's detail, carrying its module, its
# own worktree, and its wall-clock span.
attempts=$(jq -sc '[.[] | select(.obs == "moduleAttempt") | .detail]' "$ledger")

maxConcurrent=$(jq -n --argjson atts "$attempts" '
  ($atts | map({t: .startedAt, d: 1}) + ($atts | map({t: .finishedAt, d: -1}))) as $events
  | ($events | sort_by(.t) | reduce .[] as $e ({cur: 0, mx: 0};
      {cur: (.cur + $e.d), mx: ([.mx, .cur + $e.d] | max)}) | .mx)')

# attemptsSharingAWorktree: a worktree two different modules both used —
# a module's own worktree must never be shared with another module's
# (docs/parallel.md P8).
attemptsSharingAWorktree=$(jq -n --argjson atts "$attempts" '
  [$atts | group_by(.worktree)[] | select((map(.module) | unique | length) > 1)] | length')

# commitModuleOrder: the one file each lean-mend/mend commit touched, in
# commit order, with its ".lean" suffix dropped — the module it belongs
# to. Reading the touched file, not the commit message, survives a rule
# whose own `repr` (`cand.rule`) wraps onto several lines.
commitModuleOrder=$(git -C "$app" log --name-only --format= --reverse main..lean-mend/mend |
  grep -v '^$' | sed 's/\.lean$//' | jq -R . | jq -sc .)
if [ "$commitModuleOrder" = "$canonicalOrder" ]; then commitsInTopologicalOrder=true
else commitsInTopologicalOrder=false
fi

# mendBranchWritersOtherThanDriver: every lean-mend/mend commit the driver
# itself makes (`commitAccepted`) carries an "Entrenchment: " trailer line;
# a commit without it was written by something else (docs/parallel.md P11).
totalCommits=$(git -C "$app" rev-list --count main..lean-mend/mend)
markedCommits=$(git -C "$app" log --format=%B main..lean-mend/mend | grep -c '^Entrenchment: ' || true)
mendBranchWritersOtherThanDriver=$((totalCommits - markedCommits))

failed=0
[ "$maxConcurrent" -ge 2 ] || failed=$((failed + 1))
[ "$attemptsSharingAWorktree" -eq 0 ] || failed=$((failed + 1))
[ "$mendBranchWritersOtherThanDriver" -eq 0 ] || failed=$((failed + 1))
[ "$commitsInTopologicalOrder" = true ] || failed=$((failed + 1))
[ "$ledgerMatchesSequentialOrder" = true ] || failed=$((failed + 1))
if [ "$failed" -eq 0 ]; then ok=true; else ok=false; fi

jq -nc \
  --argjson maxConcurrent "$maxConcurrent" \
  --argjson attemptsSharingAWorktree "$attemptsSharingAWorktree" \
  --argjson mendBranchWritersOtherThanDriver "$mendBranchWritersOtherThanDriver" \
  --argjson commitsInTopologicalOrder "$commitsInTopologicalOrder" \
  --argjson ledgerMatchesSequentialOrder "$ledgerMatchesSequentialOrder" \
  --argjson failed "$failed" \
  --argjson ok "$ok" \
  '{max_concurrent_attempts: $maxConcurrent, attempts_sharing_a_worktree: $attemptsSharingAWorktree,
    mend_branch_writers_other_than_driver: $mendBranchWritersOtherThanDriver,
    commits_in_topological_order: $commitsInTopologicalOrder,
    ledger_matches_sequential_order: $ledgerMatchesSequentialOrder,
    failed: $failed, ok: $ok}'

[ "$ok" = true ]
