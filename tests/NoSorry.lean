import Lean
import LeanMend

/-!
Fails if any `LeanMend` constant depends on `sorryAx`, by the method of
`#print axioms`. The gate runs it with `lake env lean tests/NoSorry.lean`.
A text search cannot do this: `forbiddenTokens` names `sorry` as data.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut bad : Array Name := #[]
  for (n, _) in env.constants.toList do
    if (`LeanMend).isPrefixOf n then
      if (← liftCoreM (collectAxioms n)).contains ``sorryAx then
        bad := bad.push n
  unless bad.isEmpty do
    throwError "these constants depend on sorryAx: {bad}"
