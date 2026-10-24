import Lean.Data.Json
import LeanMend.Spec.Types

/-!
# Parse at the edge

Raw JSON becomes typed operands here, once (concept B2, stratum 3). Nothing
in `Core` sees `Json`. Each parser returns `Except String`, and the message
names the field that failed. See `docs/architecture.md` § The version boundary
for the probe's JSON, and `tests/fixtures/diagnostics/` for `lean --json`.
-/

namespace LeanMend.Parse

open Lean (Json)

private def field {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"field '{k}': {e}"

def severity : String → Except String Severity
  | "error" => .ok .error
  | "warning" => .ok .warning
  | "information" => .ok .information
  | s => .error s!"unknown severity '{s}'"

/-- One line of `lean --json` output. `module` is not in the JSON; the shell
knows which module it compiled. -/
def diagnostic (module : String) (j : Json) : Except String Diagnostic := do
  let pos ← field (α := Json) j "pos"
  let endPos ← field (α := Json) j "endPos"
  pure {
    module
    line := ← field pos "line"
    column := ← field pos "column"
    endLine := ← field endPos "line"
    endColumn := ← field endPos "column"
    severity := ← severity (← field j "severity")
    kind := ← field j "kind"
    text := ← field j "data" }

def declKind : String → Except String DeclKind
  | "theorem" => .ok .theorem
  | "def" => .ok .def
  | "instance" => .ok .instance
  | "abbrev" => .ok .abbrev
  | "axiom" => .ok .axiom
  | "other" => .ok .other
  | s => .error s!"unknown declaration kind '{s}'"

/-- The hash lean-mend stores for a region's text: `String.hash`, as hex. The
shell computes it under lean-mend's own toolchain, so one function hashes the
baseline and the after certificate. -/
def textHash (s : String) : String :=
  String.ofList (Nat.toDigits 16 s.hash.toNat)

/-- The axiom set of a declaration, as `compare` sees it: sorted, without
duplicates, and with every generated `native_decide` axiom
(`X._native.native_decide.ax_1_12`) collapsed to the one name
`native_decide`. Lean numbers those axioms per declaration, so their names can
change between toolchains when the trust does not. -/
def axiomSet (raw : List String) : List String :=
  let norm := raw.map fun a =>
    if (a.splitOn "._native.native_decide.ax_").length > 1 then "native_decide" else a
  (norm.eraseDups.toArray.qsort (· < ·)).toList

/-- One line of the probe's `decls` output. `norm` rewrites region text
before it is hashed (`AliasMap.normalize`), so the same alias map applies to
the baseline and the after certificate. -/
def decl (norm : String → String) (j : Json) : Except String Decl := do
  pure {
    name := ← field j "name"
    module := ← field j "module"
    kind := ← declKind (← field j "kind")
    statementHash := textHash (norm (← field j "statement"))
    bodyHash := textHash (norm (← field j "body"))
    axioms := axiomSet (← field j "axioms") }

/-- One line of the probe's `deprecated` output: old name and new name. A
deprecation with no new name gives no alias. -/
def alias_ (j : Json) : Except String (Option (String × String)) := do
  let n : String ← field j "name"
  let new? : Option String ← field j "newName"
  pure (new?.map (n, ·))

/-- Parse every non-empty line of `out` with `p`. The error names the line. -/
def lines {α} (p : Json → Except String α) (out : String) : Except String (List α) :=
  (out.splitOn "\n" |>.filter (· ≠ "")).zipIdx.mapM fun (l, i) =>
    match Json.parse l >>= p with
    | .ok v => .ok v
    | .error e => .error s!"line {i + 1}: {e}"

end LeanMend.Parse
