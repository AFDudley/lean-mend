# tests/lib/

Shared code that the check scripts under `tests/` source.

- `report.sh` — the check-script report contract (`docs/process.md` § Check
  scripts). A runner sources it first; then `pass NAME` and `failed NAME`
  record one check, and `report` prints one JSON object on stdout
  (`runner`, `checks`, `passed`, `failed`) and exits 1 if a check failed.
  All other output goes to stderr. An exophial spec observes the object
  (`stdout_json`); an exit code alone is a vacuous check.

A new runner must source `report.sh` and end with `report`.
