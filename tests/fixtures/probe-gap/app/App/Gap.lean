import Dep

/-! A proof that breaks after a use of a tactic that this file declares.
The probe parses with the environment of the imports only, so the command
that uses `gap_triv` does not parse, and no parsed command contains the
`simpa` that dep v2 breaks (tests/probe-gap.sh). -/

macro "gap_triv" : tactic => `(tactic| trivial)

namespace App

open Dep

theorem g (P : Nat → Prop) (h : P foo) : True ∧ P 1 :=
  ⟨by gap_triv, by simpa using h⟩

end App
