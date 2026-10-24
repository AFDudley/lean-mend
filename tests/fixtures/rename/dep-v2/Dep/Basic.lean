namespace Dep
def new (n : Nat) : Nat := n
@[deprecated Dep.new (since := "2026-01-01")]
def old := @Dep.new
end Dep
