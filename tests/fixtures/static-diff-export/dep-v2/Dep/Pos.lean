import Dep.Basic

/-! The dependency at v2: `f_pos` moved here from `Dep.Basic`, with a proof
by contradiction. -/
namespace Dep

theorem f_pos (n : Nat) : 0 < f n :=
  Classical.byContradiction fun h => h (Nat.succ_pos n)

end Dep
