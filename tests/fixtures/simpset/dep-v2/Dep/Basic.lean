namespace Dep
def foo : Nat := 1
theorem foo_eq : foo = 1 := rfl
def bar : Nat := 2
@[simp] theorem bar_eq : bar = 2 := rfl
end Dep
