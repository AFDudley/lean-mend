#!/usr/bin/env bash
# tests/cert-generated.sh: the certificate holds only the declarations that
# the source declares, at both toolchains (docs/verification.md § The
# certificate). A constant that the compiler generates is never a row, so a
# Lean version that generates different constants does not break the
# invariant.
#
# tests/fixtures/cert-generated/app is an app at Lean v4.29.0. Its module
# App.T has a `structure` with `deriving Inhabited`, as
# `Stele.DiffTest.Pools` of EquiVM, a `structure` with `deriving Repr, BEq`,
# an `inductive` with `deriving BEq, Repr, DecidableEq`, a `class` with a
# field, and unnamed instances of several shapes. At v4.29.0, Lean makes
# `App.instInhabitedPools.default` with a declaration range. At v4.33.1, it
# has no range. The module App.Inst has 18 unnamed instances of more shapes.
# The bump commit only sets v4.33.1.
#
# The run must end done with no finding. Both certificates must hold the
# declarations that App.T and App.Inst declare, and nothing else. The names
# of the unnamed instances are the names that Lean gives them at both
# toolchains (docs/verification.md § The certificate). With the probe of
# EquiVM run 9 (lean-mend 48346f7e), the baseline also had rows for
# `App.instInhabitedPools`, `App.instInhabitedPools.default`, `App.Size.mk`
# and `App.Size.size`, and the run halted with invariantBroken at App.T.
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"
root="$(cd "$(dirname "$0")/.." && pwd)"
source "$root/tests/lib/lean-mend.sh"
fx="$root/tests/fixtures/cert-generated"
work="$root/.scratch/cert-generated"
export GIT_AUTHOR_NAME=t GIT_AUTHOR_EMAIL=t@lean-mend GIT_COMMITTER_NAME=t GIT_COMMITTER_EMAIL=t@lean-mend

rm -rf "$work" && mkdir -p "$work"
app="$work/app"
cp -r "$fx/app" "$app"
printf '/.lake\n/.lean-mend\nlake-manifest.json\n' > "$app/.gitignore"
echo "leanprover/lean4:v4.29.0" > "$app/lean-toolchain"
git -C "$app" init -q -b main && git -C "$app" add -A && git -C "$app" commit -q -m "app at v4.29.0"
echo "leanprover/lean4:v4.33.1" > "$app/lean-toolchain"
git -C "$app" commit -qam "bump to v4.33.1"

out=$("$bin" run "$app" --adopt) || true
echo "$out"
[ -n "$out" ] || out='{}'
if jq -e '.state == "done" and .residue == [] and ((.findings // []) == [])' <<<"$out" >/dev/null
then pass "generated constants differ between toolchains: the run is done with no finding"
else failed "generated constants differ between toolchains: the run is done with no finding"; fi

# The declarations that the source declares. App.T: four types, six unnamed
# instances and one theorem. App.Inst: five types, one def and 18 unnamed
# instances, with the names in its comments.
expected='["App.Color","App.Pools","App.Size","App.Stats","App.instAppendPools",
  "App.instHAddPoolsNat","App.instOfNatPools","App.instSizeFin","App.instSizeList",
  "App.instSizePools","App.pools_words",
  "App.Inst.Size","App.Inst.Pos","App.Inst.Pools","App.Inst.Box","App.Inst.Tree",
  "App.Inst.IsEven","App.Inst.instSizeBox","App.Inst.instCoeNatPools",
  "App.Inst.instSizeForallNat","App.Inst.instSizeProdNatPools",
  "App.Inst.instDecidablePredNatIsEven","App.Inst.instDecidableIsEven",
  "App.Inst.instDecidableLtOfNat_app","App.Inst.instFunctorBox",
  "App.Inst.instInhabitedPools","App.Inst.instSizeBool","App.Inst.instToStringPools",
  "App.Inst.instReprBoxNat","App.Inst.instSizeTree","App.Inst.instPosPools",
  "App.Inst.instCommutativeNatHAdd_app","App.Inst.instInhabitedForallNat_app",
  "App.Inst.instPosOption","instSizeString"]'
for side in base after; do
  if jq -e --argjson want "$expected" --arg side "$side" \
      '([.[$side].decls[]?.name] | sort) == ($want | sort)' "$app/.lean-mend/session.json" >/dev/null
  then pass "the $side certificate holds only the declarations that the source declares"
  else failed "the $side certificate holds only the declarations that the source declares"; fi
done
report
