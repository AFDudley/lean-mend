#!/usr/bin/env bash
# Decision D11 on tests/fixtures/binder, bumped from Lean v4.29.0 to v4.33.1:
# by default lean-mend reports the type narrowing and leaves the module as
# residue; with --annotate-binders it narrows the binders and reports the type
# change as a warning.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/.lake/build/bin/lean-mend"
work="$root/.scratch/binder"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then echo "ok   $1"; else echo "FAIL $1"; echo "$3"; fail=1; fi
}
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$root/tests/fixtures/binder" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
g add -A && g commit -q -m "bump to v4.33.1"

out=$("$bin" run "$app" --adopt)
check "default: App.Rel is residue, and a warning names the narrowing it would apply" \
  '(.residue | index("App.Rel") != null) and (.warnings | any(test("would narrow") and test("--annotate-binders")))' "$out"
n=$(g rev-list --count main..lean-mend/mend)
[ "$n" = 0 ] && echo "ok   default: no commit" || { echo "FAIL default commits: $n"; fail=1; }

rm -rf "$app/.lean-mend" && g switch -q main && g branch -q -D lean-mend/mend
out=$("$bin" run "$app" --adopt --annotate-binders)
check "--annotate-binders: done, no residue, and the type change is a warning" \
  '.state == "done" and .residue == [] and (.warnings | any(test("type App.R") and test("changed")))' "$out"
grep -q '| mk {s t : _} : R a s t' "$app/App/Rel.lean" && grep -q '| step {s t : _} :' "$app/App/Rel.lean" \
  && echo "ok   --annotate-binders: both constructors narrowed in one edit" || { echo "FAIL source"; cat "$app/App/Rel.lean"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && echo "ok   the mended app builds at v4.33.1" || { echo "FAIL build"; fail=1; }
exit $fail
