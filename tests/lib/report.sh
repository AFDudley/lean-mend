# The check-script report contract (docs/process.md § Check scripts).
# A runner sources this file first. Then its stdout carries one JSON object
# and nothing else:
#   {"runner": NAME, "checks": [{"name": …, "ok": …}, …], "passed": N, "failed": N}
# All other output goes to stderr. `pass NAME` and `failed NAME` record one
# check; `report` prints the object and exits 1 if a check failed.
exec 3>&1 1>&2
_checks=()
_passed=0
_failed=0
pass() {
  echo "ok   $1"
  _checks+=("$(jq -cn --arg n "$1" '{name: $n, ok: true}')")
  _passed=$((_passed + 1))
}
failed() {
  echo "FAIL $1"
  _checks+=("$(jq -cn --arg n "$1" '{name: $n, ok: false}')")
  _failed=$((_failed + 1))
  fail=1
}
report() {
  local IFS=,
  printf '{"runner":"%s","checks":[%s],"passed":%d,"failed":%d}\n' \
    "$(basename "$0" .sh)" "${_checks[*]}" "$_passed" "$_failed" >&3
  exit $((_failed > 0))
}
