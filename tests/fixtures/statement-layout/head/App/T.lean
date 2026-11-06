/-! The bump commit's text: the statement of `add_zero_right` differs from
the base only in layout, the line break after the colon removed and one
space added. Its tokens are the same, so the certificate finds no change. -/
namespace App

theorem add_zero_right (n : Nat) :  n + 0 = n := rfl

end App
