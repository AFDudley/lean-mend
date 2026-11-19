import Dep

/-! Decision D17: the same heartbeat timeout as
`tests/fixtures/heartbeat-raise`, except `unroll` is a member of a `mutual`
block. `set_option maxHeartbeats … in` before `unroll`'s own start is a
parse error (`.scratch/ax-s4-measure/App2.lean`); the repair needs the
`mutual` keyword's own start (`App3.lean`). -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000

namespace App

mutual
theorem unroll : Dep.f Dep.n = Dep.n := by
  simp [Dep.f, Dep.n]

theorem companion : True := trivial
end

end App
