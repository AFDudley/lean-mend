#!/usr/bin/env bash
# Runs probe/Probe.lean under every supported toolchain against
# tests/fixtures/probe-basic, and checks its output.
# See docs/architecture.md § The version boundary.
# Usage: tests/probe-matrix.sh [toolchain…]   (default: the supported set)
set -euo pipefail
source "$(dirname "$0")/lib/report.sh"

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
  echo '{"modules": [["Fx.Uses", "Fx/Uses.lean"]], "rows": ["Fx.half", "Fx.succLe", "Fx.two"], "roots": ["Fx.em_use", "Fx.nope"]}' \
    > "$dir/explain.json"
  explain=$(run explain "$dir/explain.json")
  # The body ranges of the three definitions, from `explain`'s rows.
  ranges=$(jq -r 'select(.name == "Fx.half" or .name == "Fx.succLe" or .name == "Fx.two") | "\(.name) \(.bodyRange[0]) \(.bodyRange[1])"' <<<"$explain" | sort)
  proofs=$(run proofs Fx/Uses.lean $(awk '{print $2, $3}' <<<"$ranges"))
  # The text of each proof range, in the order of `ranges`: Fx.half, Fx.succLe, Fx.two.
  proofText=$(jq -r '.proofs[] | "\(.[0]) \(.[1])"' <<<"$proofs" | while read -r a z; do
    head -c "$z" "$dir/Fx/Uses.lean" | tail -c "$((z - a))"; echo; done)

  check() {  # check <description> <jq filter> <input>
    if jq -e -s "$2" <<<"$3" >/dev/null; then pass "$v $1"
    else failed "$v $1"; echo "$3"; fail=1; fi
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
  check "decision D17: a mutual member's mutualStart is the mutual keyword's own start, shared by every member and strictly before each member's own range" \
    '(map(select(.name == "Fx.isEven" or .name == "Fx.isOdd"))) as $ms
     | ($ms | length) == 2 and ($ms[0].mutualStart != null) and ($ms[0].mutualStart == $ms[1].mutualStart)
       and ($ms | all(.mutualStart < .range[0]))' "$uregions"
  check "decision D17: a declaration outside a mutual block has no mutualStart" \
    'map(select(.name == "Fx.double")) | length == 1 and .[0].mutualStart == null' "$basic"
  check "types are in decls with their kind; their generated constants are not" \
    '(map({(.name): .kind}) | add) as $k
     | $k["Fx.Color"] == "inductive" and $k["Fx.Pt"] == "structure" and $k["Fx.HasZero"] == "class"
       and ([$k | keys[] | select(test("casesOn|recOn|\\.rec$|\\.mk$|Pt\\.x$|Color\\.red$"))] | length) == 0' "$basic"
  check "deriving-generated constants are not in decls" \
    'map(.name) | (index("Fx.instReprPt") == null) and (index("Fx.instBEqPt") == null)' "$basic"
  check "an axiom has a row: its signature, and an empty body" \
    'map(select(.name == "Fx.zero_eq_zero"))[0] | .kind == "axiom" and .body == "" and .statementTokens[0] == ":"' "$uses"
  check "a _root_ declaration has a row under its root name" \
    'map(select(.name == "fx_true")) | length == 1' "$uses"
  check "a theorem that a command macro makes has a row, with each token once" \
    'map(select(.name == "Fx.double_one"))[0].statementTokens == [":", "double", "1", "=", "2"]' "$uses"
  check "decls gives a row for every declaration it selects: no unread line" \
    'map(select(has("unread"))) | length == 0' "$basic
$uses"
  check "deprecated alias" \
    'map(select(.name == "Fx.Old.f"))[0].newName == "Fx.New.f"' "$deprecated"
  check "explain: a row for each named declaration, with its body" \
    'map(select(.name == "Fx.half"))[0].body == ":= ⟨n / 2, by omega⟩"' "$explain"
  check "explain: the closure of a root reaches Classical.choice, an axiom of Lean core" \
    '(map(select(.const == "Classical.choice"))[0] | .axiom and (.module | startswith("Init")))
     and (map(select(.const == "Fx.em_use"))[0].uses | index("Classical.em") != null)' "$explain"
  check "explain: a root that the environment does not hold is missing" \
    'map(select(.missing == "Fx.nope")) | length == 1' "$explain"
  check "explain: the .olean of a Lean core module is under the sysroot" \
    '(map(select(has("sysroot")))[0].sysroot) as $s | map(select(.moduleFile == "Init.Prelude"))[0].olean | startswith($s)' "$explain"
  if [ "$proofText" = "$(printf 'by omega\nNat.le_succ n')" ] && [ "$(jq -s 'map(.proofs | length)' <<<"$proofs" | jq -c .)" = "[1,1,0]" ]
  then pass "$v proofs: a by block and a term-mode proof are proofs; a by block that computes a number is not"
  else failed "$v proofs"; echo "$proofs"; echo "$proofText"; fail=1; fi
done

report
