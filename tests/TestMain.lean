import Tour
import ClassifyTest

/-! The `lake test` driver: every test suite, one exit code. -/

def main : IO UInt32 := do
  let failed := (← Tour.run) + (← ClassifyTest.run)
  IO.println s!"{failed} failed"
  return if failed == 0 then 0 else 1
