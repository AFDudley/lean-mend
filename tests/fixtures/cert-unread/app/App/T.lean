/-! A theorem whose statement the probe cannot parse (tests/cert-unread.sh).
The command `local_plus` is a macro of this file that expands to a
`local notation`. The probe elaborates only the commands that change how a
later command parses (`scopeKinds` in probe/Probe.lean), and `local_plus` is
not one of them. So the probe does not know the notation, the statement of
`local_sum` does not parse, and the certificate has no row for it. The run
must stop with `declUnread`, and the error names the module and the
declaration. -/
namespace App

macro "local_plus" : command => `(local notation:65 a:66 " ⊕⊕ " b:66 => a + b)

local_plus

theorem local_sum : 1 ⊕⊕ 2 = 3 := rfl

end App
