/-! An executable root: `main` at the top level, as in EquiVM's
`Tests.DiffTest.Main`. -/

def main : IO Unit := pure ()

theorem Cx.a_self (n : Nat) : n = n := rfl
