/-! The dependency at v1 (`docs/static-diff.md` § 1, slice 1). Every
lemma has a direct proof, with no axiom: v2 (`dep-v2/Dep/Basic.lean`)
declares one new package-local axiom and routes `f_congr`, `f_pos` and
`f_inner` through it, so the fixture does not chain into Lean core's own
classical-logic internals (`Classical.byContradiction`,
`Classical.propDecidable`, …), which differ between Lean v4.29.0 and
v4.33.1 for reasons unrelated to this fixture and would make
`deepestChange`'s walk continue arbitrarily far past the intended stop. -/
namespace Dep

def f (n : Nat) : Nat := n + 1

theorem f_congr {a b : Nat} (h : a = b) : f a = f b := congrArg f h

/-- In `Dep.Basic` at v1. v2 moves it to `Dep.Pos`. -/
theorem f_pos (n : Nat) : 0 < f n := Nat.succ_pos n

/-- A `def` whose value embeds a proof subterm: `export`'s proof-erased body
replaces `h` with a placeholder and keeps `n` as a real subterm. -/
def usesProof (n : Nat) (h : 0 ≤ n) : {m : Nat // 0 ≤ m} := ⟨n, h⟩

/-- The deepest changed constant in the v1-v2 chain fixture: a direct
proof at v1, no axiom. -/
theorem f_inner {a b : Nat} (h : a = b) : f a = f b := congrArg f h

/-- Forwards to `f_inner` and nothing else: its own printed axiom set
changes between v1 and v2 whenever `f_inner`'s does, with no edit to
`f_wrapper`'s own source — the same shape `Lean.instForInLoopUnitOfMonad`
forwarding to `Lean.Loop.forIn` has on EquiVM's pins. -/
theorem f_wrapper {a b : Nat} (h : a = b) : f a = f b := f_inner h

end Dep
