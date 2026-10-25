#!/usr/bin/env bash
# Decision D12 on tests/fixtures/follow, bumped from Lean v4.29.0 to v4.33.1:
# lean-mend repairs the definition's `match` (a body edit); the theorem that
# restates it in its statement is a warning by default and is changed only
# with --follow-definition-changes.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/.lake/build/bin/lean-mend"
fx="$root/tests/fixtures/follow"
work="$root/.scratch/follow-fixture"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then echo "ok   $1"; else echo "FAIL $1"; echo "$3"; fail=1; fi
}
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
mkdir -p "$app" && cp -r "$fx/App" "$fx/App.lean" "$fx/lakefile.toml" "$app/"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
g add -A && g commit -q -m "bump to v4.33.1"

out=$("$bin" run "$app" --adopt --rules "$fx/rules")
check "default: App.Pre is residue, and a warning names the statement change" \
  '(.residue | index("App.Pre") != null) and (.warnings | any(test("App.run_spec") and test("--follow-definition-changes")))' "$out"
grep -q 'match p.val with' "$app/App/Pre.lean" && grep -q '(match p with' "$app/App/Pre.lean" \
  && echo "ok   default: the definition is repaired, the statement is not" || { echo "FAIL default source"; cat "$app/App/Pre.lean"; fail=1; }

rm -rf "$app/.lean-mend" && g switch -q main && g branch -q -D lean-mend/mend
out=$("$bin" run "$app" --adopt --rules "$fx/rules" --follow-definition-changes)
# The `match p.val` repair changes the axioms of run and run_spec, so the run
# waits on Violation cards; the statement change itself is no finding.
check "--follow-definition-changes: no residue, no statement finding, the change is a warning" \
  '.state == "awaiting" and .residue == [] and ([.findings[].reason] | all(. == "LeanMend.Reason.axiomsDiffer")) and (.warnings | any(test("changed the statement of App.run_spec")))' "$out"
grep -q '(match p.val with | 1 => 10 | 2' "$app/App/Pre.lean" \
  && echo "ok   --follow-definition-changes: the statement follows the definition" || { echo "FAIL follow source"; cat "$app/App/Pre.lean"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && echo "ok   the mended app builds at v4.33.1" || { echo "FAIL build"; fail=1; }
exit $fail
