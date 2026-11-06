/-! The base text of a theorem whose statement the bump commit edits
(tests/statement-change.sh). EquiVM run 7 halted with `invariantBroken` on
`Reasoning.Theory.u256_lor_ne_zero_right`: a line break after the colon at
v4.29.0, one line at HEAD. -/
namespace App

theorem add_zero_right (n : Nat) :
    n + 0 = n := rfl

end App
