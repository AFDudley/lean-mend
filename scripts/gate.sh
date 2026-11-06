#!/usr/bin/env bash
# The lean-mend commit gate (docs/process.md § Repository gates).
# exophial runs it in the branch worktree before every merge
# (.exophial/config.yaml, gate.command). Each step fails loud.
#
# stdout carries one JSON object and nothing else, so an exophial spec can
# observe it (`stdout_json`): one key "steps.<step name>.ok" per step that
# ran, then "passed" and "failed". exophial reads a whole field path as a
# top-level key first, so `steps.<step name>.ok` resolves even when the name
# holds a dot. Every step's own output goes to stderr. The gate stops at the
# first failed step; that step is the last key, with value false.
set -uo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"
exec 3>&1 1>&2

_obj='{}'
passed=0
# record NAME OK: add the key "steps.NAME.ok" to the result object.
record() { _obj=$(jq -cn --argjson o "$_obj" --arg k "steps.$1.ok" --argjson v "$2" '$o + {($k): $v}'); }
# summary FAILED: print the result object, then the counts, on stdout.
summary() {
  jq -cn --argjson o "$_obj" --argjson p "$passed" --argjson f "$1" '$o + {passed: $p, failed: $f}' >&3
}
# step NAME COMMAND...: run COMMAND; on failure, print the summary and exit 1.
step() {
  local name=$1; shift
  echo "== $name"
  if "$@"; then
    record "$name" true; passed=$((passed + 1))
  else
    record "$name" false; summary 1; exit 1
  fi
}

boundary() {
  if grep -rnE '^import LeanMend\.Shell' LeanMend/Spec LeanMend/Core; then
    echo "FAIL: a Spec or Core module imports the shell"; return 1
  fi
}
build() { lake build && lake build lean-mend; }

step "boundary: Spec and Core import no Shell module (concept A2)" boundary
step "lake build" build
step "no LeanMend constant depends on sorryAx (docs/verification.md)" lake env lean tests/NoSorry.lean
step "lake test" lake test
step "probe matrix" tests/probe-matrix.sh
step "one probe process per module" tests/probe-serve.sh
step "diagnostics from the Lean server" tests/server-diag.sh
step "a site after a macro of the same file gets its node and its repair, on the probe-gap fixture" tests/probe-gap.sh
step "a statement that differs only in layout is no finding" \
  tests/statement-change.sh tests/fixtures/statement-layout done
step "a statement that differs in one token halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-token invariantBroken
step "a token change in a statement inside its open scope halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-scoped invariantBroken
step "a token change in a statement that uses a local notation halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-notation invariantBroken
step "a token change in a statement that does not parse in its batch halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-batch-token invariantBroken
step "a declaration the probe cannot read stops the run with declUnread" tests/cert-unread.sh
step "constants that deriving generates are no certificate row, at either toolchain" tests/cert-generated.sh
step "lean-mend baseline on a real target" tests/baseline.sh
step "lean-mend run --adopt on the rename fixture" tests/rename.sh
step "lean-mend run --adopt --rules on the simp-set fixture" tests/simpset.sh
step "rule simpa-close-transparency on the simpa-close fixture" tests/simpa-close.sh
step "the literal-form rules on the EquiVM run 5 residue shapes" tests/literal-form.sh
step "decision D11 on the binder fixture" tests/binder.sh
step "decision D12 on the follow fixture" tests/follow.sh
step "D12 body edit and statement follow as one candidate" \
  tests/follow-pair.sh tests/fixtures/follow-pair
step "site order by declaration coordinates" tests/order.sh tests/fixtures/order-first
step "speculation across candidates" tests/speculate.sh
exposure() {
  [ "$(tests/expose.sh tests/fixtures/expose-two | jq -r .verdict)" = accepted ] &&
  [ "$(tests/expose.sh tests/fixtures/expose-back | jq -r .verdict)" = rejected ]
}
step "exposure of later errors" exposure
step "a namespace move with no aliases, on the move fixture" tests/move.sh
step "parallel frontier modules" tests/fleet.sh tests/fixtures/fleet
step "dataflow scheduling across modules" tests/dataflow.sh
step "memory bound on live probe processes" tests/probe-bound.sh
step "a probe that writes the cap text and does not exit stops the run with capExceeded" tests/cap-stop.sh
step "rule simp-set-pure-prior on its fixture" tests/simp-set-pure-prior.sh
step "rule simp-set-pure-unsolved on its fixture" tests/simp-set-pure-unsolved.sh
step "rule simp-ite-nat-cond on its fixture" tests/simp-ite-nat-cond.sh
step "rule rw-proof-arg-erw on its fixture" tests/rw-proof-arg-erw.sh
step "rule rw-unsolved-simp-all on its fixture" tests/rw-unsolved-simp-all.sh
step "rule simp-unsolved-simp-all on its fixture" tests/simp-unsolved-simp-all.sh
step "rule rw-show-redundant on its fixture" tests/rw-show-redundant.sh
step "rule simp-no-progress-delete on its fixture" tests/simp-no-progress-delete.sh
step "rule heartbeat-raise on its fixture" tests/heartbeat-raise.sh
step "rule simp-set-pure-mismatch on its fixture" tests/simp-set-pure-mismatch.sh
step "rule simpa-using-bang-nested on its fixture" tests/simpa-using-bang-nested.sh
summary 0
