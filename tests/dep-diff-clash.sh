#!/usr/bin/env bash
# tests/dep-diff-clash.sh: `lean-mend dep-diff` on a target with two
# modules that each declare the literal top-level name `main`
# (`tests/fixtures/dep-diff-clash`), the same shape a target with two
# independently-built executable roots has. Neither module imports the
# other, so each builds on its own, but importing both into the one
# environment `export --closure` uses fails with Lean's own
# already-contains-`main` error. `LeanMend.Shell.DepDiff.exportRows`
# must recover: drop the colliding module, retry, and run the dropped
# one in its own call, taking the union of both calls' rows
# (`docs/static-diff.md` § 1, the design review's own "no person chooses
# roots" requirement).
#
# Acceptance: the diff reaches `Dep.f_congr` (used only from `App.lean`)
# and `Dep.f_pos` (used only from `App2.lean`), with no `--roots` or any
# other flag naming which module to use.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
fx="$root/tests/fixtures/dep-diff-clash"
depfx="$root/tests/fixtures/static-diff-export"
work="$root/.scratch/dep-diff-clash"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
dep="$work/dep"
mkdir -p "$dep"
d() { git -C "$dep" "$@"; }
cp -r "$depfx/dep-v1/." "$dep/"
d init -q -b main && d add -A && d commit -q -m "dep v1"
v1=$(d rev-parse HEAD)
rm -rf "$dep/Dep" "$dep/Dep.lean" && cp -r "$depfx/dep-v2/." "$dep/"
d add -A && d commit -q -m "dep v2"
v2=$(d rev-parse HEAD)

build_side() {  # build_side <dir> <toolchain> <dep rev>
  local dir=$1
  mkdir -p "$dir"
  cp -r "$fx/app/." "$dir/"
  echo "leanprover/lean4:$2" > "$dir/lean-toolchain"
  printf 'name = "app"\ndefaultTargets = ["App", "App2"]\n\n[[require]]\nname = "dep"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "App"\n\n[[lean_lib]]\nname = "App2"\n' \
    "$dep" "$3" > "$dir/lakefile.toml"
  (cd "$dir" && lake update >&2 && lake build -q >/dev/null)
}
build_side "$work/base" v4.29.0 "$v1"
build_side "$work/after" v4.33.1 "$v2"

check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}
entry() {  # entry <out> <name>
  jq -c --arg n "$2" '.entries[] | select(.name == $n)' <<<"$1"
}

out=$("$bin" dep-diff "$work/base" "$work/after")

congr=$(entry "$out" Dep.f_congr)
[ -n "$congr" ] && pass "Dep.f_congr, used only from App.lean, is in the diff" \
  || { failed "Dep.f_congr is missing from the diff: the clash lost App.lean's closure"; echo "$out"; fail=1; }
check "Dep.f_congr gains Classical.choice" \
  '.kind.axiomsAdded | index("Classical.choice") != null' "$congr"

pos=$(entry "$out" Dep.f_pos)
[ -n "$pos" ] && pass "Dep.f_pos, used only from App2.lean, is in the diff" \
  || { failed "Dep.f_pos is missing from the diff: the clash lost App2.lean's closure"; echo "$out"; fail=1; }
check "Dep.f_pos gains Classical.choice" \
  '.kind.axiomsAdded | index("Classical.choice") != null' "$pos"

report
