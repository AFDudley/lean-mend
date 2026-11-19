import App.Ops

/-! The base text of a theorem whose statement parses only inside the scope
of `open App.Ops` (tests/statement-change.sh). A parse with the environment
of the imports and no `open` does not parse the statement. Before the probe
read the file's own scopes, the certificate had no row for the theorem, so
the bump commit's token change was no finding. -/
open App.Ops

namespace App

theorem scoped_sum : 1 ⊞ 2 = 4 := rfl

end App
