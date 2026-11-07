/-! Paired with `Slow.lean` for `tests/dataflow.sh`: an independent module
with a fast fix. `Dep` and `Clean` import it. -/
def fastVal : Nat := 1

theorem fooF : True := by
  trivial
