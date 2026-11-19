/-! The dependency at v2 (`docs/static-diff.md` § 1, slice 1). `f_congr`,
`f_pos` and `f_inner` each route through `Classical.choice` directly
(not through `Classical.byContradiction`/`Classical.propDecidable`,
which differ between Lean v4.29.0 and v4.33.1 for reasons unrelated to
this fixture and would make `deepestChange`'s walk continue arbitrarily
far past the intended stop). `usesProof` is unchanged. -/
namespace Dep

def f (n : Nat) : Nat := n + 1

theorem f_congr {a b : Nat} (h : a = b) : f a = f b :=
  (fun (_ : True) => congrArg f h) (Classical.choice (α := True) ⟨trivial⟩)

def usesProof (n : Nat) (h : 0 ≤ n) : {m : Nat // 0 ≤ m} := ⟨n, h⟩

/-- The deepest changed constant in the v1-v2 chain fixture: gains
`Classical.choice` directly — the entry `propagate`'s `deepestChange`
must continue to, from `f_wrapper`. -/
theorem f_inner {a b : Nat} (h : a = b) : f a = f b :=
  (fun (_ : True) => congrArg f h) (Classical.choice (α := True) ⟨trivial⟩)

/-- Same source as v1: forwards to `f_inner` and nothing else. Its own
printed axiom set still changes (it now transitively uses
`Classical.choice` through `f_inner`), so it is ALSO an axioms-changed
dependency-diff entry, the nearer, wrong cause `deepestChange` must walk
past. -/
theorem f_wrapper {a b : Nat} (h : a = b) : f a = f b := f_inner h

end Dep
