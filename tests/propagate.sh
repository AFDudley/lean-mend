#!/usr/bin/env bash
# tests/propagate.sh: `lean-mend propagate` (`docs/static-diff.md` § 2,
# slice 3), on tests/fixtures/propagate: `app` (`tests/dep-diff.sh`'s own
# `App.lean`, with one more theorem that reaches no changed dependency
# constant, and one that reaches a wrapper two hops from the deepest
# changed constant) and `dep-v1`/`dep-v2` (`tests/card-cause.sh`'s own
# dependency fixture, Lean v4.29.0 and v4.33.1, plus `f_inner`/`f_wrapper`
# for the chain check), owned by this test only.
#
# Acceptance (slice 3, docs/static-diff.md § Slices): the app theorem
# through the changed lemma, `appUsesCongr`, is predicted with its path to
# `Dep.f_congr`; `appUsesPos` is predicted with its path to `Dep.f_pos`;
# the app theorem that does not reach a changed dependency constant,
# `appOwnIsOne`, is not predicted; `appUsesWrapper`, which reaches only
# `Dep.f_wrapper` (itself axioms-changed, but only because it forwards to
# `Dep.f_inner`), is predicted with cause `Dep.f_inner` and a path that
# continues through `Dep.f_wrapper`.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
source "$(dirname "$0")/lib/lean-mend.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
fx="$root/tests/fixtures/propagate"
depfx="$root/tests/fixtures/propagate"
work="$root/.scratch/propagate"
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
  printf 'name = "app"\ndefaultTargets = ["App"]\n\n[[require]]\nname = "dep"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "App"\n' \
    "$dep" "$3" > "$dir/lakefile.toml"
  (cd "$dir" && lake update >&2 && lake build -q >/dev/null)
}
build_side "$work/base" v4.29.0 "$v1"
build_side "$work/after" v4.33.1 "$v2"

check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}
axiomOf() {  # axiomOf <out> <decl>
  jq -c --arg d "$2" '.axioms[] | select(.decl == $d)' <<<"$1"
}

out=$("$bin" propagate "$work/base" "$work/after")

congr=$(axiomOf "$out" appUsesCongr)
check "appUsesCongr is predicted" '. != null' "$congr"
check "appUsesCongr's cause is Dep.f_congr" '.cause == "Dep.f_congr"' "$congr"
check "appUsesCongr gains Classical.choice" \
  '.axiomsAdded | index("Classical.choice") != null' "$congr"
check "appUsesCongr's path starts at appUsesCongr and ends at Dep.f_congr" \
  '.path[0] == "appUsesCongr" and .path[-1] == "Dep.f_congr"' "$congr"

pos=$(axiomOf "$out" appUsesPos)
check "appUsesPos is predicted" '. != null' "$pos"
check "appUsesPos's cause is Dep.f_pos" '.cause == "Dep.f_pos"' "$pos"
check "appUsesPos gains Classical.choice" \
  '.axiomsAdded | index("Classical.choice") != null' "$pos"

unrelated=$(axiomOf "$out" appOwnIsOne)
[ -z "$unrelated" ] && pass "appOwnIsOne, which does not reach a changed dependency constant, is not predicted" \
  || { failed "appOwnIsOne is predicted: $unrelated"; fail=1; }

own=$(axiomOf "$out" appOwn)
[ -z "$own" ] && pass "appOwn, a def with no theorem reaching it, is not predicted" \
  || { failed "appOwn is predicted: $own"; fail=1; }

wrapper=$(axiomOf "$out" appUsesWrapper)
check "appUsesWrapper is predicted" '. != null' "$wrapper"
check "appUsesWrapper's cause is Dep.f_inner, the deepest changed constant, not Dep.f_wrapper" \
  '.cause == "Dep.f_inner"' "$wrapper"
check "appUsesWrapper gains Classical.choice" \
  '.axiomsAdded | index("Classical.choice") != null' "$wrapper"
check "appUsesWrapper's path continues through Dep.f_wrapper to Dep.f_inner" \
  '.path[0] == "appUsesWrapper" and (.path | index("Dep.f_wrapper")) != null and .path[-1] == "Dep.f_inner"' \
  "$wrapper"

report
