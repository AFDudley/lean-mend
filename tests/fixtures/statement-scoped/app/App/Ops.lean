/-! A scoped notation (tests/statement-change.sh). It parses only where the
namespace `App.Ops` is open. -/
namespace App.Ops

scoped notation:65 a:66 " ⊞ " b:66 => a + b + 1

end App.Ops
