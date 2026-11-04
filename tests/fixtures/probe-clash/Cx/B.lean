/-! A second executable root with its own top-level `main`, as in EquiVM's
`Examples.ERC20.SpecTests`. -/

def main : IO Unit := pure ()

theorem Cx.b_self (n : Nat) : n + 0 = n := rfl
