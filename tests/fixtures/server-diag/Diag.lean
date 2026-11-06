/-! S0b (`docs/parallel.md` C4, C5): `tests/server-diag.sh` sends this module
to one probe `serve` process and changes it five times. After each change, the
runner compares the probe's messages with the messages of
`lake env lean --json` on the same text. The module starts with two errors
(`wrong_sum`, `uses_unknown`) and one linter warning (`unused_hyp`). -/

def double (n : Nat) : Nat := n + n

theorem double_eq (n : Nat) : double n = 2 * n := by
  unfold double
  omega

theorem unused_hyp (h : 1 = 1) : True := trivial

theorem wrong_sum : 1 + 1 = 3 := by decide

theorem uses_unknown (n : Nat) : n ≤ n + 1 := by
  exact unknownLemma n

theorem last_one (n : Nat) : n + 0 = n := by simp
