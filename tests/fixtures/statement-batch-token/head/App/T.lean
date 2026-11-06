/-! The bump commit's text: the statement of `zap_refl` differs from the base
in two tokens, `+ 0`. The certificate finds a changed statement, and the run
halts. -/
namespace App

theorem zap_refl (zap : Nat) : zap + 0 = zap := rfl

end App
