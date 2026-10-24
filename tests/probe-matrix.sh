#!/usr/bin/env bash
# Runs probe/Probe.lean under every supported toolchain against
# tests/fixtures/probe-basic, and checks its output.
# See docs/architecture.md § The version boundary.
# Usage: tests/probe-matrix.sh [toolchain…]   (default: the supported set)
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
toolchains=("$@")
if [ ${#toolchains[@]} -eq 0 ]; then
  toolchains=(v4.29.0 v4.33.1 v4.35.0)
fi
work="$root/.scratch/probe-matrix"
fail=0

for v in "${toolchains[@]}"; do
  tc="leanprover/lean4:$v"
  dir="$work/$v"
  rm -rf "$dir"
  mkdir -p "$dir"
  cp -r "$root/tests/fixtures/probe-basic/." "$dir/"
  echo "$tc" > "$dir/lean-toolchain"
  cp "$root/probe/Probe.lean" "$dir/Probe.lean"
  (cd "$dir" && lake build -q >/dev/null)

  run() { (cd "$dir" && lake env lean --run Probe.lean "$@"); }
  imports=$(run imports Fx/Uses.lean)
  basic=$(run decls Fx.Basic Fx/Basic.lean)
  uses=$(run decls Fx.Uses Fx/Uses.lean)
  deprecated=$(run deprecated Fx.Basic)
  regions=$(run regions Fx/Basic.lean)
  uregions=$(run regions Fx/Uses.lean)

  check() {  # check <description> <jq filter> <input>
    if jq -e -s "$2" <<<"$3" >/dev/null; then echo "ok   $v $1"
    else echo "FAIL $v $1"; echo "$3"; fail=1; fi
  }
  check "imports of Fx.Uses" 'map(.imports) == [["Fx.Basic"]]' "$imports"
  check "kinds in Fx.Basic" \
    '[.[] | {(.name): .kind}] | add | .["Fx.double"] == "def" and .["Fx.Twice"] == "abbrev" and .["Fx.double_eq"] == "theorem" and .["Fx.instInhabitedTwice"] == "instance"' "$basic"
  check "statement text" \
    'map(select(.name == "Fx.double_eq"))[0].statement == "(n : Nat) : double n = 2 * n"' "$basic"
  check "body text" \
    'map(select(.name == "Fx.double"))[0].body == ":= n + n"' "$basic"
  check "axioms" \
    '[.[] | {(.name): .axioms}] | add | (.["Fx.em_use"] | index("Classical.choice") != null) and .["Fx.double_zero"] == []' "$uses"
  check "regions agree with decls on every named declaration" \
    '(.[0] | map({(.name): [.statementRange, .bodyRange]}) | add) as $d
     | (.[1] | map(select(.name != "")) | map({(.name): [.statementRange, .bodyRange]}) | add) as $r
     | ($r | length) == 8 and ($r | to_entries | all(.value == $d[.key]))' \
    "$(jq -s -c . <<<"$basic") $(jq -s -c . <<<"$regions")"
  check "regions reports each declaration of a mutual block" \
    'map(select(.name == "Fx.isEven" or .name == "Fx.isOdd")) | length == 2 and (.[0].range != .[1].range)' "$uregions"
  check "types are in decls with their kind; their generated constants are not" \
    '(map({(.name): .kind}) | add) as $k
     | $k["Fx.Color"] == "inductive" and $k["Fx.Pt"] == "structure" and $k["Fx.HasZero"] == "class"
       and ([$k | keys[] | select(test("casesOn|recOn|\\.rec$|\\.mk$|Pt\\.x$|Color\\.red$"))] | length) == 0' "$basic"
  check "deriving-generated constants are not in decls" \
    'map(.name) | (index("Fx.instReprPt") == null) and (index("Fx.instBEqPt") == null)' "$basic"
  check "deprecated alias" \
    'map(select(.name == "Fx.Old.f"))[0].newName == "Fx.New.f"' "$deprecated"
done

exit $fail
