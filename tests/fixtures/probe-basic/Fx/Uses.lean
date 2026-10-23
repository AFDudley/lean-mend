import Fx.Basic

namespace Fx

theorem em_use (p : Prop) : p ∨ ¬p := Classical.em p

theorem double_zero : double 0 = 0 := rfl

end Fx
