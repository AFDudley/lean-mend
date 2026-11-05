#!/usr/bin/env bash
# lean-mend run --adopt on tests/fixtures/literal-form: the app moves from Lean
# v4.29.0 with dep v1 to v4.33.1 with dep v2, as the EquiVM adopt commit
# efbfb862 did. The four modules have the shapes of the EquiVM run 5 residue
# (docs/rules.md § From residue to rule). Each proposed rule must repair its
# shape, and the mended app must build:
#   SimpaLiteral  Vault/Dispatch 270          fin-simp-mismatch: simpaToExact
#   RwNotFound    SimpleAuction/Withdraw 2070  rw-not-found-simp-only
#   RwNoGoals     TinyImmutable/Constructor 934 rw-no-goals-delete
#   RwUnsolved    StringStoreLite/Getters 3314  rw-unsolved-rfl
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/literal-form"
work="$root/.scratch/literal-form"
fail=0
check() {  # check <description> <jq filter> <json>
  if jq -e "$2" <<<"$3" >/dev/null; then pass "$1"; else failed "$1"; echo "$3"; fail=1; fi
}
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work/rules"
# The rule files under test, from rules/proposed, not copies kept in the fixture.
for r in fin-simp-mismatch rw-not-found-simp-only rw-no-goals-delete rw-unsolved-rfl; do
  cp "$root/rules/proposed/$r.json" "$work/rules/"
done
app="$work/app"
cp -r "$fx/app" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
g() { git -C "$app" "$@"; }
at() {  # at <toolchain> <dep version>: the app's toolchain and dependency
  echo "leanprover/lean4:$1" > "$app/lean-toolchain"
  rm -rf "$app/dep" && cp -r "$fx/dep-$2" "$app/dep" && echo "leanprover/lean4:$1" > "$app/dep/lean-toolchain"
}
at v4.29.0 v1
g init -q -b main && g add -A && g commit -q -m "app at v4.29.0 on dep v1"
at v4.33.1 v2
g add -A && g commit -q -m "bump to v4.33.1 and dep v2"

out=$("$bin" run "$app" --adopt --rules "$work/rules")
echo "$out"
ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
check "the bump breaks each module once, in the class of its EquiVM site" \
  '[.[] | select(.obs == "diagnosed") | .detail as $d | $d.detail[] | [$d.module, .class]] | sort ==
     [["App.RwNoGoals", "LeanMend.ErrorClass.noGoals"], ["App.RwNotFound", "LeanMend.ErrorClass.tacticFailed"],
      ["App.RwUnsolved", "LeanMend.ErrorClass.unsolvedGoals"], ["App.SimpaLiteral", "LeanMend.ErrorClass.typeMismatch"]]' "$ledger"
check "the run ends with no residue and no statement finding" \
  '(.state == "done" or .state == "awaiting") and .residue == [] and ([.findings[].reason] | all(. == "LeanMend.Reason.axiomsDiffer"))' "$out"

subjects=$(g log --format=%s main..lean-mend/mend)
echo "$subjects"
has() {  # has <description> <module> <rule prefix>
  if grep -qF "lean-mend: $3" <<<"$(grep -F " in App.$2" <<<"$subjects")"; then pass "$1"
  else failed "$1"; fi
}
has "SimpaLiteral: simpaToExact is accepted in a node that holds native_decide" SimpaLiteral "fin-simp-mismatch: LeanMend.EditOp.simpaToExact"
has "RwNotFound: rw becomes simp only" RwNotFound "rw-not-found-simp-only"
has "RwNoGoals: the rw after the closed goal is deleted" RwNoGoals "rw-no-goals-delete"
has "RwUnsolved: rfl closes the literal-form goal after rw" RwUnsolved "rw-unsolved-rfl"

grep -q 'exact (show W.gt ⟨7⟩ x ≠ ⟨0⟩ by rw \[hx\]; native_decide)' "$app/App/SimpaLiteral.lean" \
  && pass "SimpaLiteral text: exact with the native_decide term kept" || { failed "SimpaLiteral text"; cat "$app/App/SimpaLiteral.lean"; }
grep -q '^  simp only \[h\]$' "$app/App/RwNotFound.lean" && ! grep -q 'show' "$app/App/RwNotFound.lean" \
  && pass "RwNotFound text: Lean's hint dropped the unused show argument" || { failed "RwNotFound text"; cat "$app/App/RwNotFound.lean"; }
! grep -q '^  rw ' "$app/App/RwNoGoals.lean" \
  && pass "RwNoGoals text: no rw tactic is left" || { failed "RwNoGoals text"; cat "$app/App/RwNoGoals.lean"; }
grep -q '^  rfl$' "$app/App/RwUnsolved.lean" \
  && pass "RwUnsolved text: rfl follows the rw" || { failed "RwUnsolved text"; cat "$app/App/RwUnsolved.lean"; }
(cd "$app" && lake build -q >/dev/null) && pass "the mended app builds" || failed "the mended app builds"
report
