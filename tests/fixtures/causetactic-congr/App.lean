/-! `docs/machine.md` § The tactic inside the site, `causeTactic`
(`docs/rules.md` § Axiom-finding rules). `xs` is a free variable, so
`Array.any` cannot compute: the only way to prove `xs.any p = xs.any
target` is Lean core's `Array.any_congr` (`Init/Data/Array/Lemmas.lean`,
`@[congr]`), which needs `p` and `target` equal pointwise — under
`Array.any`'s own binder over the array's elements. `simp only [defn]`
closes that pointwise goal and so pulls `Array.any_congr` into the
assembled proof. -/
namespace App

def target (n : Nat) : Bool := n == 0

theorem useDefn (xs : Array Nat) (p : Nat → Bool) (defn : ∀ n, p n = target n) :
    xs.any p = xs.any target := by
  simp only [defn]

end App
