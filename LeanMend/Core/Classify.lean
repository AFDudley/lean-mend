import LeanMend.Spec.Types

/-!
# Classification

`classify` maps a diagnostic to its error class. It is pure and total, and it
does not read the rule set (`docs/rules.md` § The first error classes).
-/

namespace LeanMend

/-- `s` contains `pat`. -/
private def has (s pat : String) : Bool :=
  (s.splitOn pat).length > 1

/-- The error class of a diagnostic. The order of the tests matters: the
heartbeat text also contains "timeout". -/
def classify (d : Diagnostic) : ErrorClass :=
  let t := d.text
  if has t "(deterministic) timeout" then .heartbeat
  else if has t "timeout" then .wallclock
  else if t.startsWith "unknown identifier" || t.startsWith "unknown constant" then
    .unknownIdentifier
  else if t.startsWith "unknown namespace" then .unknownNamespace
  else if has t "failed to synthesize" && has t "Decidable" then .missingDecidable
  else if t.startsWith "type mismatch" then .typeMismatch
  else if t.startsWith "simp made no progress" then .simpNoProgress
  else if t.startsWith "unsolved goals" then .unsolvedGoals
  else .unknown

/-- A wall-clock timeout is the host's fault, so no rule edits the target for
it (`docs/machine.md` § Timeouts). -/
def ErrorClass.editable : ErrorClass → Bool
  | .wallclock | .unknown => false
  | _ => true

end LeanMend
