import Dep

/-- Declares the literal top-level name `main`, like a real Lean
executable root. `App2.lean` declares the same name: importing both in
one environment is the collision `LeanMend.Shell.DepDiff.exportRows`
must recover from. -/
def main : IO UInt32 := pure 0

/-- Uses `Dep.f_congr`: the union of the recovered export calls must
reach it. -/
theorem appUsesCongr {a b : Nat} (h : a = b) : Dep.f a = Dep.f b := Dep.f_congr h
