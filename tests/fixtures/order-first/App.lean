/-! Two declarations (`docs/parallel.md` X1, X2). `tests/order.sh` breaks both
at once, then checks that lean-mend gives up on `earlyVal` first, not
`lateVal`. -/
def earlyVal : Nat := 1 + 1

def lateVal : Nat := 2 + 2
