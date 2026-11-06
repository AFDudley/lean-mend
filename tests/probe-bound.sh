#!/usr/bin/env bash
# tests/probe-bound.sh: the memory limit on the lean-mend process tree
# (docs/parallel.md P17, P24, slice S5). tests/fixtures/probe-bound breaks
# four independent modules in one commit. Each module's rule has two
# candidates: the first keeps the break, the second fixes it with a slow
# decided count. So each module holds its probe for two attempts, and the
# four mends overlap when the limit admits them.
#
# Each work item is charged 10 GiB (Core/Sched.lean, workEstimate). When
# something runs, an admission needs the driver plus the charges of the
# running work and of the new probe within the limit (admits_within), so a
# limit of 21 GiB admits at most 2 live probes. Five runs of the fixture:
# - bounded:   --max-memory 21. From the ledger: every admission is within
#   the limit by both the charged and the measured total, or nothing ran;
#   at most 2 probes are live at any time, from the probeStart and
#   probeStop times.
# - reference: --max-memory 64, which admits all 4 probes. More than 2
#   probes are live at one time, so the bounded case has an effect. A test
#   barrier in the fixture (see tests/fixtures/probe-bound/ModA.lean) makes
#   this true at any host load: the first attempts of ModA, ModB and ModC
#   each wait until all three started. The runner sets FIXTURE_BARRIER_DIR
#   only for this case. The bounded and speculate cases admit fewer than 3
#   probes at once, so there the barrier would not end.
# - speculate: --max-memory 1 --speculate 3. The limit is below one charge,
#   so each probe starts only when nothing runs (the progress rule), and a
#   round gets no nested probe. The run must finish.
# - default:   no flag. The limit is MemAvailable minus the 16 GiB reserve.
# - capped:    --probe-cap 1200. Lean stops the first probe at its lean -M
#   cap of 1200 MiB, and the run stops with the typed error capExceeded,
#   which names the module, the cap and the peak. No process outside the
#   run stops: the runner's own shell lives on, and no probe of the run is
#   left.
# Each finished run's branch tree equals the expected tree: main's tree with
# each module replaced by the hand-written file in expected/. Each finished
# run commits the modules in the canonical order.
#
# stdout carries one JSON object and nothing else (tests/lib/report.sh).
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/probe-bound"
work="$root/.scratch/probe-bound"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
# Only the reference case below may see the barrier's marker directory.
unset FIXTURE_BARRIER_DIR
gib=$((1024 * 1024))

rm -rf "$work"
mkdir -p "$work"

# setup APP: a building app, then one commit that breaks all four modules.
setup() {
  local app="$1" m
  mkdir -p "$app"
  cp "$fx/lakefile.toml" "$app/lakefile.toml"
  cat "$root/lean-toolchain" > "$app/lean-toolchain"
  printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
  for m in A B C D; do printf 'theorem foo%s : True := by trivial\n' "$m" > "$app/Mod$m.lean"; done
  git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app builds"
  cp "$fx"/Mod?.lean "$app/"
  git -C "$app" add -A && git -C "$app" commit -q -m "break four modules"
}

# expectedTree APP: main's tree with each module replaced by expected/.
expectedTree() {
  local app="$1" idx="$1.expected.index" f sha
  GIT_INDEX_FILE="$idx" git -C "$app" read-tree main
  for f in ModA.lean ModB.lean ModC.lean ModD.lean; do
    sha=$(git -C "$app" hash-object -w "$fx/expected/$f")
    GIT_INDEX_FILE="$idx" git -C "$app" update-index --cacheinfo "100644,$sha,$f"
  done
  GIT_INDEX_FILE="$idx" git -C "$app" write-tree
}

# maxLive LEDGER: the largest count of live probes, from the probeStart and
# probeStop times. A stop at the same millisecond as a start counts first.
maxLive() {
  jq -s '[.[] | select(.obs == "probeStart") | {t: .detail.at, d: 1}] +
         [.[] | select(.obs == "probeStop") | {t: .detail.at, d: -1}]
    | sort_by(.t, .d) | reduce .[] as $e ({cur: 0, mx: 0};
        {cur: (.cur + $e.d), mx: ([.mx, .cur + $e.d] | max)}) | .mx' "$1"
}

# runCase NAME FLAGS...: run the fixture with FLAGS; check the tree, the
# commit order, and that every admission respects the limit. Sets $live to
# the largest count of live probes.
runCase() {
  local name="$1"; shift
  local app="$work/$name/app" out ledger canonical commits diagnosed
  setup "$app" >&2
  if out=$("$bin" run "$app" --adopt --rules "$fx/rules" "$@"); then :; fi
  echo "$name: $out"
  ledger="$app/.lean-mend/ledger.jsonl"
  if jq -e '.residue == [] and .state == "done"' <<<"$out" >/dev/null; then pass "$name: the run finishes with no residue"
  else failed "$name: the run finishes with no residue"; fi
  if [ "$(expectedTree "$app")" = "$(git -C "$app" rev-parse 'lean-mend/mend^{tree}')" ]; then
    pass "$name: the branch tree equals the expected tree"
  else failed "$name: the branch tree equals the expected tree"; fi
  canonical=$(jq -sc '[.[] | select(.obs == "build")][0].detail | map(split(": ")[0])' "$ledger")
  commits=$(git -C "$app" log --name-only --format= --reverse main..lean-mend/mend | grep -v '^$' |
    sed 's/\.lean$//' | uniq | jq -R . | jq -sc .)
  diagnosed=$(jq -sc '[.[] | select(.obs == "diagnosed") | .detail.module]' "$ledger")
  if [ "$commits" = "$canonical" ] && [ "$diagnosed" = "$canonical" ]; then
    pass "$name: the commits and the ledger follow the canonical order"
  else failed "$name: the commits and the ledger follow the canonical order ($commits, $diagnosed, $canonical)"; fi
  if jq -se '[.[] | select(.obs == "probeStart") | .detail] | length > 0 and
      all((.chargedKiB <= .limitKiB and .measuredKiB <= .limitKiB) or (.liveProbes == 0 and .otherWork == 0))' \
      "$ledger" >/dev/null; then
    pass "$name: every probe starts within the limit, or when nothing runs"
  else failed "$name: every probe starts within the limit, or when nothing runs"; fi
  live=$(maxLive "$ledger")
  measure "$name.max_live_probes" "$live"
  measure "$name.max_tree_kib" "$(jq -s '[.[] | select(.obs == "probeStart") | .detail.treeKiB] | max' "$ledger")"
}

runCase bounded --max-memory 21

if jq -se '.[0].obs == "memoryLimit" and .[0].detail.limitKiB == 21 * 1024 * 1024 and .[0].detail.source == "flag"
    and .[0].detail.treeLimit.mechanism != null' "$work/bounded/app/.lean-mend/ledger.jsonl" >/dev/null; then
  pass "bounded: the ledger starts with the limit of 21 GiB and the tree limit"
else failed "bounded: the ledger starts with the limit of 21 GiB and the tree limit"; fi
if [ "$live" -le 2 ]; then pass "bounded: at most 2 probes are live at any time"
else failed "bounded: at most 2 probes are live at any time ($live)"; fi

# `rm -rf "$work"` above removes the barrier markers of the last run.
mkdir -p "$work/barrier"
FIXTURE_BARRIER_DIR="$work/barrier" runCase reference --max-memory 64
if [ "$live" -gt 2 ]; then pass "reference: more than 2 probes are live at one time"
else failed "reference: more than 2 probes are live at one time ($live)"; fi

runCase speculate --max-memory 1 --speculate 3
ledger="$work/speculate/app/.lean-mend/ledger.jsonl"
if [ "$live" -le 1 ]; then pass "speculate: at most 1 probe is live at any time"
else failed "speculate: at most 1 probe is live at any time ($live)"; fi
if jq -se '[.[] | select(.obs == "speculateAttempt")] | length > 0' "$ledger" >/dev/null; then
  pass "speculate: the rounds speculate, on the module's own probe"
else failed "speculate: the rounds speculate, on the module's own probe"; fi

runCase default
memTotal=$(awk '/^MemTotal:/ {print $2}' /proc/meminfo)
if jq -se --argjson total "$memTotal" --argjson gib "$gib" '.[0].obs == "memoryLimit" and (.[0].detail |
    .source == "memAvailable" and .reserveKiB == 16 * $gib and .workEstimateKiB == 10 * $gib and
    .memAvailableKiB <= $total and .limitKiB == ([.memAvailableKiB - .reserveKiB, 0] | max))' \
    "$work/default/app/.lean-mend/ledger.jsonl" >/dev/null; then
  pass "default: the limit is MemAvailable minus the 16 GiB reserve"
else failed "default: the limit is MemAvailable minus the 16 GiB reserve"; fi

# capped: Lean stops the first probe at its cap, and the run stops with the
# typed error (exit 3), with no retry.
app="$work/capped/app"
setup "$app" >&2
code=0
out=$("$bin" run "$app" --adopt --rules "$fx/rules" --max-memory 64 --probe-cap 1200) || code=$?
echo "capped: exit $code: $out"
ledger="$app/.lean-mend/ledger.jsonl"
if [ "$code" -eq 3 ] && jq -e '.state == "halted capExceeded" and .capKiB == 1200 * 1024 and
    (.module | test("^Mod[A-D]$")) and (.peakKiB | type == "number")' <<<"$out" >/dev/null; then
  pass "capped: the run stops with capExceeded, naming the module, the cap and the peak"
else failed "capped: the run stops with capExceeded, naming the module, the cap and the peak"; fi
if jq -se '[.[] | select(.obs == "capExceeded")] | length == 1' "$ledger" >/dev/null; then
  pass "capped: the ledger records the stop one time"
else failed "capped: the ledger records the stop one time"; fi
if [ "$(git -C "$app" rev-list --count main..lean-mend/mend)" -eq 0 ]; then
  pass "capped: the run commits nothing"
else failed "capped: the run commits nothing"; fi

report
