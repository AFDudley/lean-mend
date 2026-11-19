import Dep.Basic

/-! The dependency at v2: `f_pos` moved here from `Dep.Basic`, routed
through `Classical.choice` directly (see `Dep/Basic.lean` for why, not
`Classical.byContradiction`). -/
namespace Dep

theorem f_pos (n : Nat) : 0 < f n :=
  (fun (_ : True) => Nat.succ_pos n) (Classical.choice (α := True) ⟨trivial⟩)

end Dep
