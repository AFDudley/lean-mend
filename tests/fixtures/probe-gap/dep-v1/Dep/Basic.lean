namespace Dep
def foo : Nat := 1
@[simp] theorem foo_eq : foo = 1 := rfl
end Dep
