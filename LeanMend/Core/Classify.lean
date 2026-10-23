import LeanMend.Spec.Types

/-!
# Classification

`classify` maps a diagnostic to its error class. It is pure and total, and it
does not read the rule set (`docs/rules.md` § The first error classes).

Lean's message `kind` decides first, because it does not depend on wording.
Where Lean names no kind (`[anonymous]`), the text decides, compared without
case. `tests/fixtures/diagnostics/` holds the real `lean --json` output these
tests were taken from, for v4.29.0 and v4.35.0.
-/

namespace LeanMend

/-- `s` contains `pat`, compared without case. -/
private def has (s pat : String) : Bool :=
  (s.toLower.splitOn pat.toLower).length > 1

/-- The class from Lean's named message kind, when there is one. -/
private def classOfKind (d : Diagnostic) : Option ErrorClass :=
  match d.kind with
  | "lean.unknownIdentifier._namedError" => some .unknownIdentifier
  | "runtime.maxHeartbeats" => some .heartbeat
  | "Tactic.unsolvedGoals" => some .unsolvedGoals
  | "lean.synthInstanceFailed._namedError" =>
    if has d.text "Decidable" then some .missingDecidable else some .unknown
  | _ => none

/-- The class from the message text. -/
private def classOfText (t : String) : ErrorClass :=
  if has t "(deterministic) timeout" then .heartbeat
  else if has t "timeout" then .wallclock
  else if has t "unknown identifier" || has t "unknown constant" then .unknownIdentifier
  else if has t "unknown namespace" then .unknownNamespace
  else if has t "failed to synthesize" && has t "Decidable" then .missingDecidable
  else if has t "type mismatch" then .typeMismatch
  else if has t "made no progress" then .simpNoProgress
  else if has t "unsolved goals" then .unsolvedGoals
  else .unknown

/-- The error class of a diagnostic. -/
def classify (d : Diagnostic) : ErrorClass :=
  (classOfKind d).getD (classOfText d.text)

/-- A wall-clock timeout is the host's fault, so no rule edits the target for
it (`docs/machine.md` § Timeouts). -/
def ErrorClass.editable : ErrorClass → Bool
  | .wallclock | .unknown => false
  | _ => true

end LeanMend
