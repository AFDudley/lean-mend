namespace Dep
def foo : Nat := 1
@[simp] theorem foo_eq : foo = 1 := rfl
def bar : Nat := 2
theorem bar_eq : bar = 2 := rfl
end Dep
