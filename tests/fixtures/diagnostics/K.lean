open Nonexistent.Space
def a : Nat := Old.g
def b : Nat := "s"
example : ∀ n : Nat, n + 0 = n := by intro n; simp only [Nat.mul_comm]
theorem c : 1 = 2 := by simp
structure W where v : Nat
def d (w : W) : Bool := match w with | ⟨1⟩ => true | _ => false
instance : OfNat W n := ⟨⟨n⟩⟩
def e (w : W) : Bool := if w = 1 then true else false
set_option maxHeartbeats 1 in
theorem h : (List.range 200).length = 200 := by simp
