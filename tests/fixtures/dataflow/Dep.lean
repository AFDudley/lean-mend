import Fast

/-! For `tests/dataflow.sh`: imports `Fast` only, and has its own break. It
is blocked until `Fast` builds. -/
theorem fooD : fastVal = 1 := by
  exact unknownHeadD
