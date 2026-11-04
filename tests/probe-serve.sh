#!/usr/bin/env bash
# tests/probe-serve.sh: S0a (docs/parallel.md C1-C3). Starts the probe's
# `serve` command on a fixture module, in one long-lived process, and sends
# it one request for each of three file versions. Checks that each reply's
# regions and nodes equal the output of the probe's own `regions` and `node`
# commands on the same version.
#
# stdout carries one JSON object and nothing else: {"versions": 3,
# "replies_equal": true|false, "request_wall_ms": N, "peak_rss_kb": N}.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
work="$root/.scratch/probe-serve"

rm -rf "$work"
mkdir -p "$work"
cp -r "$root/tests/fixtures/probe-basic/." "$work/"
cp "$root/probe/Probe.lean" "$work/Probe.lean"
(cd "$work" && lake build -q >/dev/null)

run() { (cd "$work" && lake env lean --run Probe.lean "$@"); }

# Three versions of Fx/Basic.lean, each a different body edit of the same
# declaration, so their byte offsets differ but the file's imports do not:
# one import should serve all three (C2).
cp "$work/Fx/Basic.lean" "$work/v1.lean"
sed 's/n + n/n + n + 0/' "$work/v1.lean" > "$work/v2.lean"
sed 's/n + n/Nat.succ n + n - 1/' "$work/v1.lean" > "$work/v3.lean"

# The expected answers, from the probe's own one-shot `regions` and `node`
# commands, computed before the long-lived `serve` process starts: a probe
# process inherits any open pipe fd of its parent shell, and one left open
# across a `lake env lean --run` call makes that call hang, so none of these
# one-shot calls run while the request/reply fifos below are open.
declare -a want_regions want_nodes offsets
for i in 0 1 2; do
  v="v$((i + 1))"
  cp "$work/$v.lean" "$work/Fx/Basic.lean"
  want_regions[i]=$(run regions Fx/Basic.lean | jq -s -c '.')
  offsets[i]=$(jq -c '[.[].statementRange[0]]' <<<"${want_regions[i]}")
  # shellcheck disable=SC2046 # the offsets are a trusted jq-produced list of numbers
  want_nodes[i]=$(run node Fx/Basic.lean $(jq -r '.[]' <<<"${offsets[i]}") | jq -s -c '.')
done

mkfifo "$work/req.fifo" "$work/rep.fifo"
(cd "$work" && exec lake env lean --run Probe.lean serve <"$work/req.fifo" >"$work/rep.fifo") &
probe_pid=$!
exec 7>"$work/req.fifo" 8<"$work/rep.fifo"

versions=0
replies_equal=true
request_wall_ms=0

for i in 0 1 2; do
  v="v$((i + 1))"
  cp "$work/$v.lean" "$work/Fx/Basic.lean"
  req=$(jq -nc --arg f "Fx/Basic.lean" --argjson o "${offsets[i]}" '{file: $f, offsets: $o}')

  start_ns=$(date +%s%N)
  echo "$req" >&7
  read -r reply <&8
  end_ns=$(date +%s%N)
  request_wall_ms=$(((end_ns - start_ns) / 1000000))

  got_regions=$(jq -c '.regions' <<<"$reply")
  got_nodes=$(jq -c '.nodes' <<<"$reply")
  if [ "$got_regions" != "${want_regions[i]}" ] || [ "$got_nodes" != "${want_nodes[i]}" ]; then
    replies_equal=false
  fi
  versions=$((versions + 1))
done

# `lake env lean --run` forks `lean` as a child of the `lake` wrapper
# (`probe_pid`), and the child, not the wrapper, holds the imported
# environment, so its resident size is the one to read.
lean_pid=""
for p in /proc/[0-9]*; do
  pid=${p#/proc/}
  ppid=$(awk '{print $4}' "$p/stat" 2>/dev/null) || continue
  if [ "$ppid" = "$probe_pid" ]; then
    lean_pid=$pid
    break
  fi
done
peak_kb=$(grep VmHWM "/proc/${lean_pid:-$probe_pid}/status" | awk '{print $2}')

# Closing the request pipe gives the probe end of file on stdin, so its
# `serve` loop returns.
exec 7>&-
wait "$probe_pid" || true
exec 8<&-

jq -nc --argjson v "$versions" --argjson r "$replies_equal" --argjson w "$request_wall_ms" --argjson p "$peak_kb" \
  '{versions: $v, replies_equal: $r, request_wall_ms: $w, peak_rss_kb: $p}'
[ "$versions" -eq 3 ] && [ "$replies_equal" = true ] && [ "$request_wall_ms" -gt 0 ] && [ "$peak_kb" -gt 0 ]
