import LeanMend.Core.Classify

/-!
# Propose

Candidates for a site, in rule order (`docs/rules.md` § Entrenchment and
order). Only derived rules exist so far: the alias map. Pure.

`AliasMap.normalize` rewrites old names to new names in a region's text. The
shell hashes statement and body text after it, at both toolchains, so an alias
rename does not count as a statement or definition change (decision D5).
-/

namespace LeanMend

/-- A character that can be part of a Lean identifier as written in source. -/
def identChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == '\'' || c == '!' || c == '?' ||
    c.val ≥ 0x80

/-- Split text into maximal runs of identifier and non-identifier characters. -/
def runs (s : String) : List String :=
  let step := fun (acc : List (Bool × List Char)) (c : Char) =>
    match acc with
    | (k, cs) :: rest => if identChar c == k then (k, c :: cs) :: rest else (identChar c, [c]) :: acc
    | [] => [(identChar c, [c])]
  (s.toList.foldl step []).reverse.map fun (_, cs) => String.ofList cs.reverse

/-- Replace every whole identifier that the map renames. -/
def AliasMap.normalize (m : AliasMap) (s : String) : String :=
  String.join <| (runs s).map fun r => (m.pairs.lookup r).getD r

/-- The first name between backticks in a diagnostic, as Lean prints an
unknown identifier: ``Unknown identifier `Dep.old` ``. -/
def identOf (d : Diagnostic) : Option String :=
  match d.text.splitOn "`" with
  | _ :: name :: _ :: _ => some name
  | _ => none

/-- The alias pair that a written identifier refers to: the same full name, or
a full name that ends with `.` and the written name (an opened namespace). -/
def AliasMap.match? (m : AliasMap) (written : String) : Option (String × String) :=
  m.pairs.find? fun (a, _) => a == written || a.endsWith ("." ++ written)

/-- Candidates for one site. An `unknownIdentifier` site whose name the alias
map renames gets one derived candidate: the final new name, fully qualified. -/
def propose (m : AliasMap) (s : Site) : List Candidate :=
  match classify s.diagnostic, identOf s.diagnostic with
  | .unknownIdentifier, some w =>
    match m.match? w with
    | some (a, b) =>
      [{ rule := s!"alias {a} → {b}", entrenchment := .derived,
         target := .aliasRename a b, start := s.start, stop := s.stop,
         replacement := b, tokens := [b] }]
    | none => []
  | _, _ => []

end LeanMend
