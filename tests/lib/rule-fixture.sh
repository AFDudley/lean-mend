# The run of one proposed rule on its fixture (docs/rules.md § The first
# error classes: each class has a fixture that shows the break and its
# repair). A runner sources tests/lib/report.sh first, then this file.
#
# rule_fixture_run RULE: tests/fixtures/RULE/ is an app that builds at Lean
# v4.29.0 and fails at v4.33.1. The app is committed at v4.29.0, then bumped
# to v4.33.1, then `lean-mend run --adopt` mends it with the one rule file
# rules/proposed/RULE.json. Sets $app (the mended app), $out (the run's
# summary) and $ledger (the ledger as one JSON array).
#
# rule_fixture_checks RULE SITES: the checks every rule runner makes. The
# bump broke SITES sites, the run ends done with no residue, the mend branch
# holds SITES commits and each is a candidate of RULE, and the mended app
# builds at v4.33.1.
source "$(dirname "${BASH_SOURCE[0]}")/lean-mend.sh"

rule_fixture_run() {
  local rule=$1
  local root="$_lm_root"
  local work="$root/.scratch/rule-$rule"
  export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend
  rm -rf "$work" && mkdir -p "$work/rules"
  app="$work/app"
  cp -r "$root/tests/fixtures/$rule" "$app"
  cp "$root/rules/proposed/$rule.json" "$work/rules/"
  printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
  echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
  git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app at v4.29.0"
  echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
  git -C "$app" add -A && git -C "$app" commit -q -m "bump to v4.33.1"
  out=$("$bin" run "$app" --adopt --rules "$work/rules")
  echo "$out"
  ledger=$(jq -s -c . "$app/.lean-mend/ledger.jsonl")
}

rule_fixture_checks() {
  local rule=$1 sites=$2
  if jq -e --argjson n "$sites" '[.[] | select(.obs == "diagnosed") | .detail.detail | length] | first == $n' <<<"$ledger" >/dev/null
  then pass "the bump to v4.33.1 breaks $sites sites"; else failed "the bump to v4.33.1 breaks $sites sites"; fi
  if jq -e '.state == "done" and .residue == []' <<<"$out" >/dev/null
  then pass "the run is done with no residue"; else failed "the run is done with no residue"; fi
  local subjects
  subjects=$(git -C "$app" log --format=%s main..lean-mend/mend)
  if [ "$(grep -c "^lean-mend: $rule: " <<<"$subjects")" = "$sites" ] && [ "$(wc -l <<<"$subjects")" = "$sites" ]
  then pass "the mend branch holds $sites commits, each a candidate of $rule"
  else failed "the mend branch holds $sites commits, each a candidate of $rule"; echo "$subjects"; fi
  if (cd "$app" && lake build -q >/dev/null)
  then pass "the mended app builds at v4.33.1"; else failed "the mended app builds at v4.33.1"; fi
}
