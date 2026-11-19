import Dep

/-! A proof that breaks after a use of a tactic that this file declares.
A parse with the environment of the imports only does not parse the command
that uses `gap_triv`. The probe reads the commands that the elaboration of
this file parsed, so the `simpa` that dep v2 breaks gets its node
(tests/probe-gap.sh). -/

macro "gap_triv" : tactic => `(tactic| trivial)

namespace App

open Dep

theorem g (P : Nat → Prop) (h : P foo) : True ∧ P 1 :=
  ⟨by gap_triv, by simpa using h⟩

end App
