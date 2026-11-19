#!/usr/bin/env bash
# tests/probe-stamp-race.sh: two `lean-mend` binaries with a DIFFERENT
# embedded `probe/Probe.lean`, run concurrently against the SAME target.
# Before `probeBuildDir` keyed the probe's build directory by its stamp,
# both binaries shared one `.lean-mend/probe/` directory: whichever one's
# `ensureProbeBuilt` ran its `lake build Probe` last left the OTHER one's
# already-started `lean --run` reading a `Probe.olean` for a different
# source, "unknown module prefix 'Probe'" (measured on the shared EquiVM
# measurement trees, 2026-11-11, three `lean-mend` binaries with three
# different embedded probes running against the same trees at once).
#
# The second binary is this source tree with one comment line added to
# `probe/Probe.lean` (a full second checkout of a real other revision
# needs a standalone clone of this package, which this worktree does not
# have — see `docs/architecture.md`; the stamp is `hash probeSource ++
# toolchain`, so a one-line source change is the same kind of difference
# a real second branch gives).
#
# Acceptance: both binaries' `baseline` calls exit 0, and the target's
# `.lean-mend/probe/` holds two build directories, one per binary's
# stamp, each with its own `Probe.olean`.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
(cd "$root" && lake build lean-mend -q) >&2
bin="$root/.lake/build/bin/lean-mend"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

work="$root/.scratch/probe-stamp-race"
rm -rf "$work" && mkdir -p "$work"

other_src="$work/other-src"
mkdir -p "$other_src"
# tar, not rsync: the gate image has no rsync.
tar -C "$root" --exclude=./.scratch --exclude=./.lake --exclude=./.git -cf - . | tar -C "$other_src" -xf -
printf '\n-- probe-stamp-race: one extra line, a different probeSource hash.\n' >> "$other_src/probe/Probe.lean"
(cd "$other_src" && lake build lean-mend -q) >&2
other_bin="$other_src/.lake/build/bin/lean-mend"

target="$work/target"
mkdir -p "$target"
cat "$root/lean-toolchain" > "$target/lean-toolchain"
printf 'name = "app"\ndefaultTargets = ["App"]\n\n[[lean_lib]]\nname = "App"\n' > "$target/lakefile.toml"
echo 'def appOwn : Nat := 1' > "$target/App.lean"
(cd "$target" && lake build -q) >&2

"$bin" baseline "$target" > "$work/new.json" 2> "$work/new.err" &
new_pid=$!
"$other_bin" baseline "$target" > "$work/other.json" 2> "$work/other.err" &
other_pid=$!
new_ok=0; other_ok=0
wait "$new_pid" && new_ok=1 || true
wait "$other_pid" && other_ok=1 || true

[ "$new_ok" = 1 ] && pass "the first binary's baseline run exits 0" \
  || { failed "the first binary's baseline run failed: $(cat "$work/new.err")"; fail=1; }
[ "$other_ok" = 1 ] && pass "the second (different probeSource) binary's baseline run exits 0" \
  || { failed "the second binary's baseline run failed: $(cat "$work/other.err")"; fail=1; }

dirs=$(find "$target/.lean-mend/probe" -maxdepth 1 -mindepth 1 -type d | wc -l)
[ "$dirs" -ge 2 ] && pass "the two binaries' probes built into two different stamp directories ($dirs found)" \
  || { failed "expected at least two probe build directories, found $dirs"; fail=1; }

report
