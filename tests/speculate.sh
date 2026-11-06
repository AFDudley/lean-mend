#!/usr/bin/env bash
# tests/speculate.sh: S4 (docs/parallel.md P14-P16). tests/fixtures/speculate
# has one open site with three candidates, in rule order: the first two
# leave the site open, and the third fixes the site. A test barrier in the
# fixture (`barrierMark` and `barrierAwaitStopped` in App.lean) makes the
# first two wait until the probe of the third stops. So the third finishes
# first at any host load, and finish_order_inverted does not depend on time.
#
# The barrier needs the three candidates in one round at the same time. The
# run gives --speculate 3 and --max-memory 64: the gate then admits two
# nested probes, so `roundPlacement` puts the third candidate on its own probe,
# which starts before the round attempts the first candidate. The runner sets
# FIXTURE_BARRIER_DIR only for that run. The sequential run attempts the
# first two candidates before the third, so there the barrier must be off.
#
# This runs the fixture once with --speculate 3 (the parallel path: every
# candidate attempts at the same time, each in its own worktree) and once
# with no flag (the sequential path: one candidate at a time, as before).
# It reads the parallel run's ledger for the concurrency and finish-order
# facts, and reads each run's mend-branch commit for the accepted candidate.
#
# stdout carries one JSON object and nothing else: {"max_concurrent_candidates",
# "distinct_worktrees", "finish_order_inverted", "accepted_index",
# "leftover_results", "leftover_worktrees", "committed_index",
# "sequential_committed_index"}.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/speculate"
work="$root/.scratch/speculate"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
# Only the parallel run below may see the barrier's marker directory.
unset FIXTURE_BARRIER_DIR

rm -rf "$work"
mkdir -p "$work"

# setup APP: a fresh two-commit fixture app at APP, a building placeholder
# then the fixture's open site, as the other S1 runners do.
setup() {
  local app="$1"
  mkdir -p "$app"
  cp "$fx/lakefile.toml" "$app/lakefile.toml"
  cat "$root/lean-toolchain" > "$app/lean-toolchain"
  printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
  cat > "$app/App.lean" << 'EOF'
theorem placeholder : True := by trivial
EOF
  git -C "$app" init -q -b main
  git -C "$app" add -A
  git -C "$app" commit -q -m "app builds"
  cp "$fx/App.lean" "$app/App.lean"
  git -C "$app" add -A
  git -C "$app" commit -q -m "break foo"
}

# committedIndex APP: the candidate's rule-order index (1, 2 or 3) whose
# known replacement text matches APP's one mend-branch commit, or 0 when
# there is not exactly one commit.
committedIndex() {
  local app="$1" n diff
  n=$(git -C "$app" rev-list --count main..lean-mend/mend)
  if [ "$n" -ne 1 ]; then echo 0; return; fi
  diff=$(git -C "$app" show --format= lean-mend/mend)
  if grep -qF '+  trivial' <<<"$diff"; then echo 3
  elif grep -qF -- '-- slow candidate 2' <<<"$diff"; then echo 2
  elif grep -qF -- '-- slow candidate 1' <<<"$diff"; then echo 1
  else echo 0
  fi
}

parApp="$work/parallel/app"
seqApp="$work/sequential/app"
setup "$parApp"
setup "$seqApp"

# A limit of 64 GiB admits the module probe and both nested probes at once
# (docs/parallel.md P24), whatever memory the host has free. `rm -rf "$work"`
# above removes the markers of the last run.
mkdir -p "$work/parallel/barrier"
FIXTURE_BARRIER_DIR="$work/parallel/barrier" \
  "$bin" run "$parApp" --adopt --rules "$fx/rules" --speculate 3 --max-memory 64 >&2 || true
"$bin" run "$seqApp" --adopt --rules "$fx/rules" >&2 || true

ledger="$parApp/.lean-mend/ledger.jsonl"
attempts=$(jq -sc '[.[] | select(.obs == "speculateAttempt") | .detail]' "$ledger")

maxConcurrent=$(jq -n --argjson atts "$attempts" '
  ($atts | map({t: .startedAt, d: 1}) + ($atts | map({t: .finishedAt, d: -1}))) as $events
  | ($events | sort_by(.t) | reduce .[] as $e ({cur: 0, mx: 0};
      {cur: (.cur + $e.d), mx: ([.mx, .cur + $e.d] | max)}) | .mx)')
distinctWorktrees=$(jq -n --argjson atts "$attempts" '$atts | map(.worktree) | unique | length')
finishOrderInverted=$(jq -n --argjson atts "$attempts" '
  (($atts | sort_by(.index) | map(.index)) != ($atts | sort_by(.finishedAt) | map(.index)))')
acceptedIndex=$(jq -sc '[.[] | select(.obs == "speculateResult") | .detail.acceptedIndex][-1]' "$ledger")

# leftover_results: the parallel run's main checkout must hold nothing but
# the accepted commit, with no uncommitted trace of a discarded candidate.
leftoverResults=$(git -C "$parApp" status --porcelain | wc -l | tr -d ' ')
# leftover_worktrees: every attempt worktree must be removed; only the main
# checkout is left.
leftoverWorktrees=$(($(git -C "$parApp" worktree list --porcelain | grep -c '^worktree ') - 1))

committedIdx=$(committedIndex "$parApp")
sequentialIdx=$(committedIndex "$seqApp")

jq -nc \
  --argjson maxConcurrent "$maxConcurrent" \
  --argjson distinctWorktrees "$distinctWorktrees" \
  --argjson finishOrderInverted "$finishOrderInverted" \
  --argjson acceptedIndex "$acceptedIndex" \
  --argjson leftoverResults "$leftoverResults" \
  --argjson leftoverWorktrees "$leftoverWorktrees" \
  --argjson committedIdx "$committedIdx" \
  --argjson sequentialIdx "$sequentialIdx" \
  '{max_concurrent_candidates: $maxConcurrent, distinct_worktrees: $distinctWorktrees,
    finish_order_inverted: $finishOrderInverted, accepted_index: $acceptedIndex,
    leftover_results: $leftoverResults, leftover_worktrees: $leftoverWorktrees,
    committed_index: $committedIdx, sequential_committed_index: $sequentialIdx}'

[ "$maxConcurrent" -ge 2 ]
[ "$distinctWorktrees" -ge 2 ]
[ "$finishOrderInverted" = true ]
[ "$acceptedIndex" -eq 3 ]
[ "$leftoverResults" -eq 0 ]
[ "$leftoverWorktrees" -eq 0 ]
[ "$committedIdx" -eq 3 ]
[ "$sequentialIdx" -eq 3 ]
