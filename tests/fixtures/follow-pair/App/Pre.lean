/-! A `match` on numerals over a `Fin`-backed type, in one declaration's
statement and in its own body. v4.29.0 accepts both; v4.33.1 cannot
synthesize `Decidable (p = 1)` in either (decision D12, X7). The form is
EVMLean's precompile `match` (Semantics.lean, Theory/AccountLocality.lean). -/
namespace App

def Size : Nat := 1461501637330902918203684832716283019655932542976

instance : NeZero Size := ⟨by unfold Size; omega⟩

abbrev Addr : Type := Fin Size

instance {n : Nat} : OfNat Addr n := ⟨Fin.ofNat _ n⟩

theorem run_pos (p : Addr) :
    0 ≤ (match p with | 1 => 10 | 2 => 20 | _ => (0 : Nat)) := by
  match p with
  | 1 => exact Nat.zero_le _
  | 2 => exact Nat.zero_le _
  | _ => exact Nat.zero_le _

end App
