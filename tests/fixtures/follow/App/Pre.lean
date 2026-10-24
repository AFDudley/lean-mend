/-! A `match` on numerals over a `Fin`-backed type, in a definition and in a
theorem's statement that restates it. v4.29.0 accepts both; v4.33.1 cannot
synthesize `Decidable (p = 1)` (decision D12). The form is EVMLean's
precompile `match` (Semantics.lean, Theory/AccountLocality.lean). -/
namespace App

def Size : Nat := 1461501637330902918203684832716283019655932542976

instance : NeZero Size := ⟨by unfold Size; omega⟩

abbrev Addr : Type := Fin Size

instance {n : Nat} : OfNat Addr n := ⟨Fin.ofNat _ n⟩

def run (p : Addr) : Nat :=
  match p with
  | 1 => 10
  | 2 => 20
  | _ => 0

theorem run_spec (p : Addr) :
    run p = (match p with | 1 => 10 | 2 => 20 | _ => 0) := rfl

end App
