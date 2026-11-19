#!/usr/bin/env bash
# A Violation card states the cause of its axiom change
# (docs/verification.md § What a card explains), on tests/fixtures/card-cause.
# The app is Lean core only and requires the git package `dep`. It is
# committed at Lean v4.29.0 on dep v1, then bumped to v4.33.1 on dep v2. The
# app's source does not change. At v2, `Dep.f_congr` gains `Classical.choice`
# (the shape of Mathlib's `List.find?_congr` in EquiVM run 10), and
# `Dep.f_pos` moves from `Dep.Basic` to `Dep.Pos` and gains it too.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/card-cause"
work="$root/.scratch/card-cause"
fail=0
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
# The dependency: one git repository, v1 then v2.
dep="$work/dep"
mkdir -p "$dep"
d() { git -C "$dep" "$@"; }
cp -r "$fx/dep-v1/." "$dep/"
d init -q -b main && d add -A && d commit -q -m "dep v1"
v1=$(d rev-parse HEAD)
rm -rf "$dep/Dep" "$dep/Dep.lean" && cp -r "$fx/dep-v2/." "$dep/"
d add -A && d commit -q -m "dep v2"
v2=$(d rev-parse HEAD)

app="$work/app"
cp -r "$fx/app" "$app"
printf '/.lake\n/.lean-mend\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
_at() {  # _at TOOLCHAIN REV: the app's toolchain and the dependency's revision, with its manifest
  echo "leanprover/lean4:$1" > "$app/lean-toolchain"
  printf 'name = "app"\ndefaultTargets = ["App"]\n\n[[require]]\nname = "dep"\ngit = "%s"\nrev = "%s"\n\n[[lean_lib]]\nname = "App"\n' \
    "$dep" "$2" > "$app/lakefile.toml"
  (cd "$app" && lake update >&2)
}
_at v4.29.0 "$v1"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0 on dep v1"
_at v4.33.1 "$v2"
g add -A && g commit -q -m "bump to v4.33.1 and dep v2"

out=$("$bin" run "$app" --adopt)
echo "$out"
cards="$app/.lean-mend/cards"
card() { grep -l -F "**Subject.** \`$1\`" "$cards"/c-*.md; }
has() {  # has <description> <file> <fixed string>…
  local desc=$1 file=$2; shift 2
  local s
  for s in "$@"; do
    if ! grep -q -F -- "$s" "$file"; then failed "$desc"; echo "missing: $s"; cat "$file"; fail=1; return; fi
  done
  pass "$desc"
}

if jq -e '.state == "awaiting" and ([.findings[] | select(.reason == "LeanMend.Reason.axiomsDiffer") | .decl] | sort) == ["App.mid", "App.t1", "App.t2", "App.t3"]' <<<"$out" >/dev/null
then pass "the run waits on four Violation cards: App.mid, App.t1, App.t2, App.t3"
else failed "four Violation cards"; fail=1; fi

t1=$(card App.t1)
has "App.t1: the path at v4.33.1 runs through the cause Dep.f_congr to Classical.choice" "$t1" \
  '- Path at leanprover/lean4:v4.33.1: `App.t1` → `App.mid` → **`Dep.f_congr`** → `Classical.byContradiction` → `Classical.propDecidable` → `Classical.choice`.'
has "App.t1: the path at v4.29.0 leads to the cause, without the axiom" "$t1" \
  '- Path at leanprover/lean4:v4.29.0 to the cause: `App.t1` → `App.mid` → **`Dep.f_congr`**. `Classical.choice` is not on it.'
has "App.t1: the cause has its module and the dep revision at each toolchain" "$t1" \
  "at leanprover/lean4:v4.33.1: \`Dep.f_congr\` in module \`Dep.Basic\` (dep $v2), axioms \`Classical.choice\`, \`Quot.sound\`, \`propext\`" \
  "at leanprover/lean4:v4.29.0: \`Dep.f_congr\` in module \`Dep.Basic\` (dep $v1), axioms none"

t3=$(card App.t3)
has "App.t3: the moved lemma Dep.f_pos is the cause, with its module at each toolchain" "$t3" \
  '- Path at leanprover/lean4:v4.33.1: `App.t3` → **`Dep.f_pos`** → `Classical.byContradiction`' \
  "at leanprover/lean4:v4.33.1: \`Dep.f_pos\` in module \`Dep.Pos\` (dep $v2), axioms \`Classical.choice\`, \`Quot.sound\`, \`propext\`" \
  "at leanprover/lean4:v4.29.0: \`Dep.f_pos\` in module \`Dep.Basic\` (dep $v1), axioms none"

causes="$cards/causes.md"
congr=$(awk '/^## Cause [0-9]+: `Dep.f_congr`/{on=1; next} /^## /{on=0} on' "$causes")
if [ "$(grep -c '^- c-[0-9]* `App\.\(mid\|t1\|t2\)`: `Classical.choice`' <<<"$congr")" = 3 ] && ! grep -q 'App.t3' <<<"$congr"
then pass "causes.md: one cause section for Dep.f_congr lists App.mid, App.t1 and App.t2"
else failed "causes.md: the Dep.f_congr section"; cat "$causes"; fail=1; fi
if [ "$(grep -c '^## Cause [0-9]*: ' "$causes")" = 2 ] && grep -q '^## Cause [0-9]*: `Dep.f_pos` in module `Dep.Pos`' "$causes"
then pass "causes.md: two causes, Dep.f_congr and Dep.f_pos"
else failed "causes.md: two causes"; cat "$causes"; fail=1; fi
if jq -e '.evidence.base.toolchain == "leanprover/lean4:v4.29.0" and (.evidence.after.consts | map(.[0]) | index("Dep.f_congr") != null)' "$app/.lean-mend/session.json" >/dev/null
then pass "session.json holds the evidence of both toolchains"
else failed "session.json evidence"; fail=1; fi
report
