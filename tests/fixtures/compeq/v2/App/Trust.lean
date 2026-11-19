/-! A `def` that applies an `@[extern]` constant (`docs/static-diff.md` § 4
step 4, decision S4): `myAdd` is never recursed into, only compared by
name — a stated trust point. -/
namespace App

@[extern "app_my_add"]
def myAdd (a b : Nat) : Nat := a + b

def usesTrust (n : Nat) : Nat := let j := myAdd n 1; j

end App
