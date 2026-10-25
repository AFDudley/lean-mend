import Lean
import LeanMend

/-!
Fails if any `LeanMend` constant depends on `sorryAx`, by the method of
`#print axioms`. The gate runs it with `lake env lean tests/NoSorry.lean`.
A text search cannot do this: `forbiddenTokens` names `sorry` as data.

stdout carries one JSON object (docs/process.md § Check scripts):
`{"runner": "NoSorry", "checked": N, "sorry_dependents": [names]}`, where
`checked` is the number of `LeanMend` constants read.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut bad : Array Name := #[]
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    if (`LeanMend).isPrefixOf n then
      checked := checked + 1
      if (← liftCoreM (collectAxioms n)).contains ``sorryAx then
        bad := bad.push n
  let names := Json.arr (bad.map fun n => Json.str n.toString)
  IO.println (Json.mkObj [("runner", "NoSorry"), ("checked", toJson checked),
    ("sorry_dependents", names)]).compress
  unless bad.isEmpty do
    throwError "these constants depend on sorryAx: {bad}"
