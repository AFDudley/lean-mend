/-! The dependency at v2. `pick` now routes its `ite` through
`Classical.propDecidable`, so it depends on `Classical.choice` (as the
decidability instance for `Dep.pick`'s own `if`, mirroring how Mathlib's
`backward.match.sparseCases` default moves a classical instance into a
compiled match at Lean v4.33.1). `pickC` keeps the v1 computable value,
under a new name: the shape `replaceInBody` targets (`docs/rules.md` §
Edit operations). -/
namespace Dep

noncomputable def pick : Nat :=
  @ite Nat True (Classical.propDecidable True) 5 0

def pickC : Nat := 5

end Dep
