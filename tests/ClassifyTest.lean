import LeanMend
import LeanMend.Shell.Parse

/-!
# Classification of real diagnostics

`tests/fixtures/diagnostics/<toolchain>.jsonl` is the error output of
`lean --json K.lean` under that toolchain, recorded unchanged. Each line must
parse, and each must get the class below. Line numbers refer to `K.lean`.
-/

open LeanMend

namespace ClassifyTest

def expected : List (Nat × ErrorClass) :=
  [(1, .unknownNamespace), (2, .unknownIdentifier), (3, .typeMismatch),
   (4, .simpNoProgress), (5, .unsolvedGoals), (9, .missingDecidable),
   (11, .heartbeat), (14, .noGoals)]

def run : IO Nat := do
  let mut failed := 0
  for v in ["v4.29.0", "v4.35.0"] do
    let out ← IO.FS.readFile s!"tests/fixtures/diagnostics/{v}.jsonl"
    match Parse.lines (Parse.diagnostic "K") out with
    | .error e =>
      IO.println s!"FAIL {v} parse: {e}"; failed := failed + 1
    | .ok ds =>
      let got := ds.map fun d => (d.line, classify d)
      for (line, want) in expected do
        match got.lookup line with
        | some c =>
          let ok := c == want
          IO.println s!"{if ok then "ok  " else "FAIL"} {v} line {line}: {repr c}"
          unless ok do failed := failed + 1
        | none => IO.println s!"FAIL {v} line {line}: no diagnostic"; failed := failed + 1
  -- A deprecated-module warning from Lean v4.33.1 (EVMLean Conform/Wheels.lean)
  -- has `"endPos": null`; it must parse, with the range at its start.
  let out ← IO.FS.readFile "tests/fixtures/diagnostics/null-endpos.jsonl"
  match Parse.lines (Parse.diagnostic "W") out with
  | .ok [d] =>
    let ok := d.endLine == d.line && d.endColumn == d.column && d.severity == .warning
    IO.println s!"{if ok then "ok  " else "FAIL"} null endPos parses, range at its start"
    unless ok do failed := failed + 1
  | .ok ds => IO.println s!"FAIL null endPos: {ds.length} diagnostics"; failed := failed + 1
  | .error e => IO.println s!"FAIL null endPos: {e}"; failed := failed + 1
  return failed

end ClassifyTest
