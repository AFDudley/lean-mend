import App.Ops

/-! The bump commit's text: the statement of `scoped_sum` differs from the
base in one token, `1` changed to `0` and the result to `3`. The
certificate finds a changed statement, and the run halts. -/
open App.Ops

namespace App

theorem scoped_sum : 0 ⊞ 2 = 3 := rfl

end App
