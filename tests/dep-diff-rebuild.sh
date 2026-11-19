#!/usr/bin/env bash
# tests/dep-diff-rebuild.sh: law LM3 (docs/laws.md, input closure) for
# `lean-mend dep-diff`. A stored dependency diff is read again only under a
# key that covers every input of the diff. A rebuild of the after side that
# changes a dependency's built .olean, with the same toolchain, the same
# lake-manifest.json and the same module list, changes an input.
#
# The fixture is tests/dep-diff.sh's own (tests/fixtures/dep-diff,
# tests/fixtures/static-diff-export). The first call stores a diff in which
# `Dep.f_congr` gains `Classical.choice`. The runner then writes v1's
# constructive proof of `Dep.f_congr` into the after side's checkout of the
# dependency (.lake/packages/dep) and rebuilds the after side: the manifest
# revision and the module list do not change, and `Dep.f_congr`'s built
# axiom set does. The second call must compute a new diff, in which
# `Dep.f_congr` is not an axioms-changed entry.
#
# This runner is not a step of scripts/gate.sh yet. It is red until the key
# covers the built files; the change that makes it green adds the step.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
fx="$root/tests/fixtures/dep-diff"
depfx="$root/tests/fixtures/static-diff-export"
work="$root/.scratch/dep-diff-rebuild"
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
  printf 'name = "app"\ndefaultTargets = ["App"]\n\n[[require]]\nname = "dep"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "App"\n' \
    "$dep" "$3" > "$dir/lakefile.toml"
  (cd "$dir" && lake update >&2 && lake build -q >/dev/null)
}
build_side "$work/base" v4.29.0 "$v1"
build_side "$work/after" v4.33.1 "$v2"

congrTag() {  # congrTag <out>: the kind tag of Dep.f_congr's entry, or "none"
  jq -r '[.entries[] | select(.name == "Dep.f_congr") | .kind.tag] | first // "none"' <<<"$1"
}

out1=$("$bin" dep-diff "$work/base" "$work/after")
if [ "$(congrTag "$out1")" = axioms ]; then pass "the first call lists Dep.f_congr as an axioms-changed entry"
else failed "the first call lists Dep.f_congr as an axioms-changed entry"; echo "$out1"; fi

# Rebuild the after side with v1's proof of Dep.f_congr in its dependency
# checkout. The manifest, the toolchain and the module list stay the same.
pkg="$work/after/.lake/packages/dep/Dep/Basic.lean"
manifest_before=$(sha256sum "$work/after/lake-manifest.json")
sed -i 's/^  Classical.byContradiction fun hne => hne (congrArg f h)$/  congrArg f h/' "$pkg"
grep -q '^  congrArg f h$' "$pkg"
(cd "$work/after" && lake build -q >/dev/null)
[ "$manifest_before" = "$(sha256sum "$work/after/lake-manifest.json")" ]

out2=$("$bin" dep-diff "$work/base" "$work/after")
if jq -e '.cached == false' <<<"$out2" >/dev/null; then
  pass "a rebuilt after side with the same module list gives a fresh diff"
else failed "a rebuilt after side with the same module list gives a fresh diff"; echo "$out2"; fi
if [ "$(congrTag "$out2")" != axioms ]; then
  pass "after the rebuild, Dep.f_congr is not an axioms-changed entry"
else failed "after the rebuild, Dep.f_congr is not an axioms-changed entry"; fi

report
