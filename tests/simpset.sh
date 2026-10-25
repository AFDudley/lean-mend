#!/usr/bin/env bash
# lean-mend run --adopt --rules on tests/fixtures/simpset: dep v2 drops @[simp]
# from foo_eq and adds it to bar_eq. Three proofs break in three classes; one
# ratified rule per class repairs each (docs/rules.md § Edit operations).
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
bin="$root/.lake/build/bin/lean-mend"
fx="$root/tests/fixtures/simpset"
work="$root/.scratch/simpset"
tc="leanprover/lean4:v4.33.1"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then echo "ok   $1"; else echo "FAIL $1"; echo "$3"; fail=1; fi
}
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$fx/app" "$app" && echo "$tc" > "$app/lean-toolchain"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
cp -r "$fx/dep-v1" "$app/dep"
g() { git -C "$app" "$@"; }
g init -q -b main && g add -A && g commit -q -m "app on dep v1"
rm -rf "$app/dep" && cp -r "$fx/dep-v2" "$app/dep"
g add -A && g commit -q -m "bump dep to v2"

out=$("$bin" run "$app" --adopt --rules "$fx/rules")
echo "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
# a3's proof now closes by `simp` with bar_eq, which uses propext; in v1 `rfl`
# closed it with no axiom. The proof is valid, but its axiom set grew, so the
# invariant asks a person: one Violation card. App.Lint is repaired by Lean's
# hint (below), so nothing is residue.
check "the run awaits one Violation card for App.a3, with no residue" \
  '.state == "awaiting" and .residue == [] and .findings == [{"card":"LeanMend.CardKind.violation","decl":"App.a3","reason":"LeanMend.Reason.axiomsDiffer"}]' "$out"
check "App.Use: three sites in three classes" \
  'map(select(.obs == "diagnosed" and .detail.module == "App.Use"))[0].detail.detail | map(.class) | sort ==
     ["LeanMend.ErrorClass.noGoals", "LeanMend.ErrorClass.typeMismatch", "LeanMend.ErrorClass.unsolvedGoals"]' "$ledger"
check "App.Use: the first candidate of each rule was accepted (errors 3 → 2 → 1 → 0)" \
  '[.[] | select(.obs == "rebuilt" and (.detail.rule | startswith("no-progress") | not)) | .detail.errors] == [2, 1, 0]' "$ledger"
check "App.Lint: the first candidate cleared the error with one unused simp argument, and Lean's hint made the accepted candidate" \
  '[.[] | select(.obs == "rebuilt" and (.detail.rule | startswith("no-progress")))] as $r
   | ($r | length) == 2 and $r[0].detail.errors == 0 and $r[0].detail.lint == 1 and $r[0].detail.unused == ["Nat.add_zero"]
     and $r[1].detail.lint == 0 and ($r[1].detail.rule | test("Lean.s hint"))' "$ledger"
grep -q 'simp \[Dep.foo_eq\]$' "$app/App/Lint.lean" && echo "ok   App.Lint is simp [Dep.foo_eq]: the unused argument is gone" || { echo "FAIL App.Lint text"; cat "$app/App/Lint.lean"; fail=1; }
src=$(cat "$app/App/Use.lean")
grep -q 'simp \[Dep.foo_eq\]' <<<"$src" && echo "ok   a1: simp gained Dep.foo_eq" || { echo "FAIL a1"; fail=1; }
grep -q 'exact h' <<<"$src" && echo "ok   a2: simpa became exact h" || { echo "FAIL a2"; fail=1; }
! grep -qE '^\s+rfl\s*$' <<<"$src" && echo "ok   a3: the rfl after the closed goal is gone" || { echo "FAIL a3"; fail=1; }
n=$(git -C "$app" rev-list --count main..lean-mend/mend)
[ "$n" = 4 ] && echo "ok   four commits on lean-mend/mend" || { echo "FAIL commits: $n"; fail=1; }
(cd "$app" && lake build -q >/dev/null) && echo "ok   the mended app builds" || { echo "FAIL build"; fail=1; }

# The card loop: list the open card, read its evidence, accept it.
cards=$("$bin" cards "$app")
grep -q '^c-1 violation App.a3 ' <<<"$cards" && echo "ok   cards lists c-1, a violation card for App.a3" || { echo "FAIL cards: $cards"; fail=1; }
grep -q 'baseline axioms: \[\]' "$app/.lean-mend/cards/c-1.md" && grep -q 'after axioms: \[propext\]' "$app/.lean-mend/cards/c-1.md" \
  && echo "ok   the card shows the axiom evidence ([] -> [propext])" || { echo "FAIL card text"; cat "$app/.lean-mend/cards/c-1.md"; fail=1; }
out=$("$bin" judge "$app" c-1 accept --by tester)
check "accepting c-1 moves the run to done" '.state == "done" and .residue == []' "$out"
[ -z "$("$bin" cards "$app")" ] && echo "ok   no open card is left" || { echo "FAIL open cards left"; fail=1; }
if "$bin" judge "$app" c-1 accept --by tester >/dev/null; then echo "FAIL a second judgment on c-1 was accepted"; fail=1
else echo "ok   a second judgment on c-1 is refused"; fi

# Without the rules, every site is residue.
rm -rf "$app/.lean-mend" && g switch -q main && g branch -q -D lean-mend/mend
out=$("$bin" run "$app" --adopt)
check "without rules: done, App.Use residue" '.state == "done" and (.residue | index("App.Use") != null)' "$out"
exit $fail
