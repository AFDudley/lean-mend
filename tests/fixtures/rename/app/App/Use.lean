import Dep

/-! Uses a name that the dependency renames between v1 and v3. -/
namespace App

def three : Nat := Dep.old 3

theorem three_eq : three = 3 := rfl

theorem old_id (n : Nat) : Dep.old n = n := rfl

end App
