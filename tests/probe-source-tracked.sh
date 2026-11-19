#!/usr/bin/env bash
# tests/probe-source-tracked.sh: `Shell/Target.lean` embeds
# `probe/Probe.lean`'s text at compile time (`include_str`), which Lake's
# own import analysis does not see. Before `lakefile.lean`'s `input_file
# probeSrc` and `LeanMend`'s `needs := #[`@/probeSrc]`, editing
# `probe/Probe.lean` alone and running `lake build lean-mend` could
# silently reuse a stale compiled `Target.olean` with the OLD embedded
# probe source: no error, no rebuild, wrong behavior only visible at a
# scale small fixtures do not reach (measured 2026-11-11, EquiVM's own
# pins: a `strings` check on the built binary showed no trace of an edit
# made minutes earlier).
#
# Acceptance: in a scratch copy of this package, append one line to
# `probe/Probe.lean`, run `lake build lean-mend`, and find that line's
# exact text in the built binary with `strings`.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
fail=0

work="$root/.scratch/probe-source-tracked"
rm -rf "$work" && mkdir -p "$work"
# tar, not rsync: the gate image has no rsync.
tar -C "$root" --exclude=./.scratch --exclude=./.lake --exclude=./.git -cf - . | tar -C "$work" -xf -

(cd "$work" && lake build lean-mend -q) >&2

marker="probe-source-tracked-marker-line-$$-$(date +%s%N)"
echo "-- $marker" >> "$work/probe/Probe.lean"
(cd "$work" && lake build lean-mend -q) >&2

bin="$work/.lake/build/bin/lean-mend"
# `grep -q` exits on its first match, which sends `strings` a SIGPIPE;
# under `pipefail` that makes the whole pipeline's exit status the
# broken-pipe failure, not the match. `grep -c` reads to the end, so it
# does not trigger this.
count=$(strings "$bin" | grep -cF -- "$marker")
if [ "$count" -gt 0 ]; then
  pass "a one-line edit to probe/Probe.lean, followed by a plain lake build, reaches the compiled binary"
else
  failed "the marker line added to probe/Probe.lean is not in the built binary: the compiled probe is stale"
  fail=1
fi

report
