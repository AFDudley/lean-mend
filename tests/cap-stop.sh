#!/usr/bin/env bash
# tests/cap-stop.sh: the stop of a run at a probe's memory cap
# (docs/parallel.md P24, § The memory limit). tests/fixtures/cap-stop breaks
# two independent modules, Capped and Held, in one commit. Each module's
# rule has one candidate, which adds an #eval after the theorem:
# - Held's probe writes the marker `held` and then waits 600 s. It gives no
#   reply and does not exit.
# - Capped's probe waits for the marker `held`, writes the marker `capped`
#   and the text of the lean -M cap to its stderr, and then waits 600 s. It
#   gives no reply and does not exit.
# A run of 2026-11-06 saw probes that wrote the cap text and did not exit;
# the run then made no progress for 3600 s. Here the driver must end the
# capped probe at its cap text, end the held probe at the stop of the run,
# wait for its tasks, and exit 3 with capExceeded, within seconds of the cap
# text. A driver that does not end the probes ends only after the 600 s
# waits, and the check of the stop time fails.
#
# stdout carries one JSON object and nothing else (tests/lib/report.sh).
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/cap-stop"
work="$root/.scratch/cap-stop"
app="$work/app"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work"
mkdir -p "$app" "$work/markers"
export CAP_STOP_DIR="$work/markers"

# A building app, then one commit that breaks both modules.
cp "$fx/lakefile.toml" "$app/lakefile.toml"
cat "$root/lean-toolchain" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
for m in Capped Held; do printf 'theorem foo%s : True := by trivial\n' "$m" > "$app/$m.lean"; done
git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app builds"
cp "$fx"/Capped.lean "$fx"/Held.lean "$app/"
git -C "$app" add -A && git -C "$app" commit -q -m "break two modules"

# --max-memory 64 admits both probes at once.
code=0
start=$(date +%s.%N)
out=$("$bin" run "$app" --adopt --rules "$fx/rules" --max-memory 64) || code=$?
end=$(date +%s.%N)
echo "cap-stop: exit $code: $out"
ledger="$app/.lean-mend/ledger.jsonl"

if [ "$code" -eq 3 ] && jq -e '.state == "halted capExceeded" and .module == "Capped" and
    .capKiB == 15 * 1024 * 1024 and (.peakKiB | type == "number")' <<<"$out" >/dev/null; then
  pass "the run stops with capExceeded, naming the module Capped"
else failed "the run stops with capExceeded, naming the module Capped"; fi
if jq -se '[.[] | select(.obs == "capExceeded")] | length == 1 and .[0].detail.module == "Capped"' \
    "$ledger" >/dev/null; then
  pass "the ledger records the stop one time"
else failed "the ledger records the stop one time"; fi

# The time from the cap text (the marker `capped`, written just before it)
# to the exit of lean-mend.
if [ -f "$CAP_STOP_DIR/capped" ] && [ -f "$CAP_STOP_DIR/held" ]; then
  stop=$(echo "$end - $(stat -c %.9Y "$CAP_STOP_DIR/capped")" | bc)
  measure stop_seconds "$stop"
  if [ "$(echo "$stop < 60" | bc)" -eq 1 ]; then pass "the run exits within 60 s of the cap text"
  else failed "the run exits within 60 s of the cap text ($stop s)"; fi
else failed "the run exits within 60 s of the cap text (no marker capped or held)"; fi
measure wall_seconds "$(echo "$end - $start" | bc)"

# No process of the run is left: no process works in the app or its
# worktrees, and the held probe is gone.
left=""
for p in /proc/[0-9]*; do
  case "$(readlink "$p/cwd" 2>/dev/null)" in "$app"|"$app"/*) left="$left ${p#/proc/}" ;; esac
done
held=$(cat "$CAP_STOP_DIR/held" 2>/dev/null || echo none)
if [ -z "$left" ] && [ "$held" != none ] && [ ! -e "/proc/$held" ]; then
  pass "no probe of the run is left"
else failed "no probe of the run is left (processes:$left; held probe $held)"; fi
if [ "$(git -C "$app" worktree list --porcelain | grep -c '/.lean-mend/mend/')" -eq 0 ]; then
  pass "the run removes the worktrees of its mends"
else failed "the run removes the worktrees of its mends"; fi
if [ "$(git -C "$app" rev-list --count main..lean-mend/mend)" -eq 0 ]; then
  pass "the run commits nothing"
else failed "the run commits nothing"; fi

report
