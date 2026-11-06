/-! The bump commit's text: the statement of `add_zero_right` differs from
the base in one token, `+` changed to `-`, with the base's layout. The
certificate finds a changed statement, and the run halts. -/
namespace App

theorem add_zero_right (n : Nat) :
    n - 0 = n := rfl

end App
