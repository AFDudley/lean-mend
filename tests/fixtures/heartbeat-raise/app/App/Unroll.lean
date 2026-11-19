import Dep

/-! EquiVM `Examples/UniswapV2Pair/PermitDecode.lean` 97: a `simp` that
needs more than the heartbeat limit after the bump. The fixture scales the
limit down from Lean's default 200000 to 2000, so the build stays fast. With
dep v1 the `simp` needs less than 2000; with dep v2 it needs more. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 2000

namespace App

theorem unroll : Dep.f Dep.n = Dep.n := by
  simp [Dep.f, Dep.n]

end App
