#!/usr/bin/env bash
# tests/dep-diff.sh: `lean-mend dep-diff` (`docs/static-diff.md` § 1,
# slice 2), on tests/fixtures/dep-diff and tests/fixtures/static-diff-export
# (the dependency: `tests/card-cause.sh`'s own fixture, Lean v4.29.0's
# `dep-v1` and v4.33.1's `dep-v2`). `app` requires the git package `dep`, so
# `dep` resolves under `.lake/packages/dep` with a manifest revision, the
# shape card-cause's own owner resolution reads
# (`LeanMend.Shell.Cause.ownerOfOlean`). `base` is `app` on `dep` v1 at Lean
# v4.29.0; `after` is `app` on `dep` v2 at Lean v4.33.1: two independent
# built trees of the same target, `dep-diff`'s own input shape.
#
# Acceptance (slice 2): the diff lists `Dep.f_congr` (gains
# `Classical.choice`) and `Dep.f_pos` (gains `Classical.choice` and moves
# from `Dep.Basic` to `Dep.Pos`). `App.appOwn`, the target's own
# declaration, is not in the diff. A second call reads the stored result
# instead of exporting again.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
fx="$root/tests/fixtures/dep-diff"
depfx="$root/tests/fixtures/static-diff-export"
work="$root/.scratch/dep-diff"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
# The dependency: one git repository, v1 then v2 (`tests/card-cause.sh`'s
# own pattern), so each side's manifest names a real commit revision.
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
  printf 'name = "app"\ndefaultTargets = ["App"]\n\n[[require]]\nname = "dep"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "App"\n' \
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

out1=$("$bin" dep-diff "$work/base" "$work/after")
check "the first call is not from the cache" '.cached == false' "$out1"
cache_file=$(jq -r '.cacheFile' <<<"$out1")
[ -f "$cache_file" ] && pass "the cache file exists after the first call" \
  || { failed "cache file missing: $cache_file"; fail=1; }

congr=$(entry "$out1" Dep.f_congr)
check "Dep.f_congr is an axioms-changed entry" '.kind.tag == "axioms"' "$congr"
check "Dep.f_congr gains Classical.choice" \
  '.kind.axiomsAdded | index("Classical.choice") != null' "$congr"
check "Dep.f_congr stays in Dep.Basic at both sides" \
  '.before.module == "Dep.Basic" and .after.module == "Dep.Basic"' "$congr"
check "Dep.f_congr's owner is the dep package, at its revision at each side" \
  "$(printf '.before.owner == ["dep","%s"] and .after.owner == ["dep","%s"]' "$v1" "$v2")" "$congr"

pos=$(entry "$out1" Dep.f_pos)
check "Dep.f_pos is an axioms-changed entry" '.kind.tag == "axioms"' "$pos"
check "Dep.f_pos gains Classical.choice" \
  '.kind.axiomsAdded | index("Classical.choice") != null' "$pos"
check "Dep.f_pos moves from Dep.Basic to Dep.Pos" \
  '.before.module == "Dep.Basic" and .after.module == "Dep.Pos"' "$pos"

own=$(entry "$out1" App.appOwn)
[ -z "$own" ] && pass "the target's own declaration, App.appOwn, is not in the diff" \
  || { failed "App.appOwn is in the diff: $own"; fail=1; }

up=$(entry "$out1" Dep.usesProof)
[ -z "$up" ] && pass "an unchanged dependency constant, Dep.usesProof, is not in the diff" \
  || { failed "Dep.usesProof is in the diff: $up"; fail=1; }

out2=$("$bin" dep-diff "$work/base" "$work/after")
check "the second call reads the stored result" '.cached == true' "$out2"
e1=$(jq -cS '.entries' <<<"$out1")
e2=$(jq -cS '.entries' <<<"$out2")
[ "$e1" = "$e2" ] && pass "the second call's entries equal the first call's" \
  || { failed "entries differ between calls"; fail=1; }

# A new, built module in `after` (its own module list, decision S2's
# soundness, the design review's own check): no pin change. The next
# call must not read the cache entry scoped to the old module list.
echo 'def unused : Nat := 2' > "$work/after/AppUnused.lean"
printf 'name = "app"\ndefaultTargets = ["App", "AppUnused"]\n\n[[require]]\nname = "dep"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "App"\n\n[[lean_lib]]\nname = "AppUnused"\n' \
  "$dep" "$v2" > "$work/after/lakefile.toml"
(cd "$work/after" && lake build -q >/dev/null)
out3=$("$bin" dep-diff "$work/base" "$work/after")
check "a new built module in after busts the cache: the third call is not from the cache" \
  '.cached == false' "$out3"
cache_file3=$(jq -r '.cacheFile' <<<"$out3")
[ "$cache_file3" != "$cache_file" ] && pass "the new module's cache file is a different file" \
  || { failed "the new-module call reused the old cache file: $cache_file3"; fail=1; }

report
