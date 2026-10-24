import Fx.Basic

namespace Fx

theorem em_use (p : Prop) : p ∨ ¬p := Classical.em p

theorem double_zero : double 0 = 0 := rfl

mutual
def isEven : Nat → Bool
  | 0 => true
  | n + 1 => isOdd n
def isOdd : Nat → Bool
  | 0 => false
  | n + 1 => isEven n
end

end Fx
