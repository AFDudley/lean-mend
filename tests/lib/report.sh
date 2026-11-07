# The check-script report contract (docs/process.md § Check scripts).
# A runner sources this file first. Then its stdout carries one JSON object
# and nothing else:
#   {"runner": NAME, "checks.<check name>.ok": true|false, ..., "passed": N, "failed": N}
# exophial reads a whole field path as a top-level key first, so
# `checks.<check name>.ok` resolves even when the name holds a dot. All other
# output goes to stderr. `pass NAME` and `failed NAME` record one check; a
# name recorded twice is false if either record failed. `report` prints the
# object and exits 1 if a check failed. `measure NAME N` records one measured
# number as the key "measures.<NAME>"; a measure is not a check.
exec 3>&1 1>&2
_obj='{}'
_passed=0
_failed=0
_record() {
  _obj=$(jq -cn --argjson o "$_obj" --arg k "checks.$1.ok" --argjson v "$2" \
    'if $o | has($k) then $o + {($k): ($o[$k] and $v)} else $o + {($k): $v} end')
}
pass() {
  echo "ok   $1"
  _record "$1" true
  _passed=$((_passed + 1))
}
failed() {
  echo "FAIL $1"
  _record "$1" false
  _failed=$((_failed + 1))
  fail=1
}
measure() {
  echo "measure $1 = $2"
  _obj=$(jq -cn --argjson o "$_obj" --arg k "measures.$1" --argjson v "$2" '$o + {($k): $v}')
}
report() {
  jq -cn --arg r "$(basename "$0" .sh)" --argjson o "$_obj" --argjson p "$_passed" \
    --argjson f "$_failed" '{runner: $r} + $o + {passed: $p, failed: $f}' >&3
  exit $((_failed > 0))
}
