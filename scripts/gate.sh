#!/usr/bin/env bash
# The lean-mend commit gate (docs/process.md § Repository gates).
# exophial runs it in the branch worktree before every merge
# (.exophial/config.yaml, gate.command). Each step fails loud.
#
# stdout carries one JSON object and nothing else, so an exophial spec can
# observe it (`stdout_json`): one key "steps.<step name>.ok" per step that
# ran, then "passed" and "failed". exophial reads a whole field path as a
# top-level key first, so `steps.<step name>.ok` resolves even when the name
# holds a dot. Every step's own output goes to stderr. A serial step stops
# the gate when it fails; that step is the last key, with value false. The
# steps of a parallel group (`pstep`, `pwait`) all run, and the gate stops
# after the group when one of them failed.
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

# The parallel group: fixture runners that share no state. Each runner works
# in its own `.scratch/<name>` directory with its own fixture repositories,
# and `tests/lib/lean-mend.sh`'s `lake build lean-mend` finds the binary that
# the "lake build" step already built. Runners that measure time or memory, or
# that test parallel work themselves, are serial steps, not in a group.
# GROUP_JOBS runners run at a time. Measured 2026-11-12: run one after
# another, lean-mend's gate took 2462 s in the gate image, and the image
# build that runs it went over the 3600 s gate.timeout.
GROUP_JOBS=6
_gdir=$(mktemp -d)
_gnames=()
# pstep NAME COMMAND...: start COMMAND in the group; its output goes to a file.
pstep() {
  local name=$1; shift
  while [ "$(jobs -rp | wc -l)" -ge "$GROUP_JOBS" ]; do wait -n; done
  local i=${#_gnames[@]}
  _gnames+=("$name")
  ( "$@" > "$_gdir/$i.log" 2>&1; echo $? > "$_gdir/$i.rc" ) &
}
# pwait: wait for the group; print each step's output in order, record each
# step, and stop the gate if one failed.
pwait() {
  wait
  local i failed=0
  for i in "${!_gnames[@]}"; do
    echo "== ${_gnames[$i]}"
    cat "$_gdir/$i.log"
    if [ "$(cat "$_gdir/$i.rc")" = 0 ]; then
      record "${_gnames[$i]}" true; passed=$((passed + 1))
    else
      record "${_gnames[$i]}" false; failed=1
    fi
  done
  _gnames=()
  if [ "$failed" = 1 ]; then summary 1; exit 1; fi
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
step "no catch branch replaces a result: each one throws (law LM5)" lake env lean tests/CatchRethrow.lean
step "lake test" lake test
step "probe matrix" tests/probe-matrix.sh
exposure() {
  [ "$(tests/expose.sh tests/fixtures/expose-two | jq -r .verdict)" = accepted ] &&
  [ "$(tests/expose.sh tests/fixtures/expose-back | jq -r .verdict)" = rejected ]
}

# Fixture runners, GROUP_JOBS at a time.
pstep "a second run of the same bump reuses the baseline worktree and its stored certificate, with the same result (law LM3)" \
  tests/base-reuse.sh
pstep "export lists a lemma that gains Classical.choice and one that moves module, on the static-diff-export fixture" \
  tests/static-diff-export.sh
pstep "lean-mend dep-diff lists the changed dependency lemmas of two pins and caches the result, on the dep-diff fixture" \
  tests/dep-diff.sh
pstep "lean-mend dep-diff reaches every target module through a main-name clash, by the union of recovered export calls" \
  tests/dep-diff-clash.sh
pstep "lean-mend dep-diff computes a fresh diff after a rebuild that changes a built file, with the same manifest and module list (law LM3)" \
  tests/dep-diff-rebuild.sh
pstep "causeTactic returns the simp step that pulls in a congr lemma, on the causetactic-congr fixture" \
  tests/causetactic.sh
pstep "a site after a macro of the same file gets its node and its repair, on the probe-gap fixture" tests/probe-gap.sh
pstep "a statement that differs only in layout is no finding" \
  tests/statement-change.sh tests/fixtures/statement-layout done
pstep "a statement that differs in one token halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-token invariantBroken
pstep "a token change in a statement inside its open scope halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-scoped invariantBroken
pstep "a token change in a statement that uses a local notation halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-notation invariantBroken
pstep "a token change in a statement that does not parse in its batch halts with invariantBroken" \
  tests/statement-change.sh tests/fixtures/statement-batch-token invariantBroken
pstep "a declaration the probe cannot read stops the run with declUnread" tests/cert-unread.sh
pstep "constants that deriving generates are no certificate row, at either toolchain" tests/cert-generated.sh
pstep "lean-mend baseline on a real target" tests/baseline.sh
pstep "lean-mend run --adopt on the rename fixture" tests/rename.sh
pstep "lean-mend run --adopt --rules on the simp-set fixture" tests/simpset.sh
pstep "rule simpa-close-transparency on the simpa-close fixture" tests/simpa-close.sh
pstep "the literal-form rules on the EquiVM run 5 residue shapes" tests/literal-form.sh
pstep "decision D11 on the binder fixture" tests/binder.sh
pstep "decision D12 on the follow fixture" tests/follow.sh
pstep "a Violation card names the path and the changed dependency lemma, on the card-cause fixture" tests/card-cause.sh
pstep "a Behavior card names the diff, the commit and its rule, and the proof check, on the card-body fixture" tests/card-body.sh
pstep "a Behavior finding that changes a proof only auto-accepts, no card, on the card-body App.checked shape" tests/proof-only-accept.sh
pstep "D12 body edit and statement follow as one candidate" \
  tests/follow-pair.sh tests/fixtures/follow-pair
pstep "site order by declaration coordinates" tests/order.sh tests/fixtures/order-first
pstep "exposure of later errors" exposure
pstep "a namespace move with no aliases, on the move fixture" tests/move.sh
pstep "rule simp-set-pure-prior on its fixture" tests/simp-set-pure-prior.sh
pstep "rule simp-set-pure-unsolved on its fixture" tests/simp-set-pure-unsolved.sh
pstep "rule simp-ite-nat-cond on its fixture" tests/simp-ite-nat-cond.sh
pstep "rule rw-proof-arg-erw on its fixture" tests/rw-proof-arg-erw.sh
pstep "rule rw-unsolved-simp-all on its fixture" tests/rw-unsolved-simp-all.sh
pstep "rule simp-unsolved-simp-all on its fixture" tests/simp-unsolved-simp-all.sh
pstep "rule rw-show-redundant on its fixture" tests/rw-show-redundant.sh
pstep "rule simp-no-progress-delete on its fixture" tests/simp-no-progress-delete.sh
pstep "rule heartbeat-raise on its fixture" tests/heartbeat-raise.sh
pstep "decision D17: beforeDecl before the mutual keyword, on a mutual-nested heartbeat site" tests/mutual-before-decl.sh
pstep "rule simp-set-pure-mismatch on its fixture" tests/simp-set-pure-mismatch.sh
pstep "rule simpa-using-bang-nested on its fixture" tests/simpa-using-bang-nested.sh
pstep "Level 3, a proof-only repair closes both findings by the walk (decision D15)" tests/level3-proof-only.sh
pstep "Level 3, a computation-changing repair closes the axiom finding by a rebuild, leaving one Behavior card (decisions D15, D16)" tests/level3-computation.sh
pstep "propagation predicts the app theorems that reach a changed dependency lemma, with their paths, and not the one that does not (static-diff.md S2)" tests/propagate.sh
pstep "a one-line edit to probe/Probe.lean reaches the built lean-mend binary through a plain lake build (input_file dependency tracking)" tests/probe-source-tracked.sh
pwait

# Serial: these runners measure time or memory, or test parallel work themselves.
step "one probe process per module" tests/probe-serve.sh
step "diagnostics from the Lean server" tests/server-diag.sh
step "speculation across candidates" tests/speculate.sh
step "parallel frontier modules" tests/fleet.sh tests/fixtures/fleet
step "dataflow scheduling across modules" tests/dataflow.sh
step "memory bound on live probe processes" tests/probe-bound.sh
step "a probe that writes the cap text and does not exit stops the run with capExceeded" tests/cap-stop.sh
summary 0
