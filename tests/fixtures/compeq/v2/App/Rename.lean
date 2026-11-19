/-! A `def` whose own local variable name changes between the two
toolchains, outside its statement (`docs/static-diff.md` § 4). The
statement token sequence, `(n : Nat) : Nat`, is unchanged, so the finding
is a Behavior one. The body bytes change (not inside a proof, decision
D16's own test gives no auto-accept), but the elaborated, proof-erased
term is identical: a bound variable's name does not change its de Bruijn
depth. -/
namespace App

def renamed (n : Nat) : Nat := let j := n + 1; j + 1

end App
