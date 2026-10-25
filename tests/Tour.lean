import LeanMend

/-!
# The tour

One run of the pure machine that fires every level-1 and level-2 transition
(concept D7). The observations stand for what the shell would see on a
two-module target: `A` breaks, one candidate repairs it, and `B` (which
imports `A`) then fails with no candidate and becomes residue.
-/

open LeanMend

def tc (n : String) : Toolchain := ⟨n⟩

def declA (body : String) : Decl :=
  { name := "A.f", module := "A", kind := .def, statementHash := "s1",
    bodyHash := body, axioms := ["propext"] }

def declB : Decl :=
  { name := "B.t", module := "B", kind := .theorem, statementHash := "s2",
    bodyHash := "b2", axioms := [] }

def site (m : String) : Site :=
  { diagnostic := { module := m, line := 3, column := 2, endLine := 3, endColumn := 7,
                    severity := .error, kind := "lean.unknownIdentifier._namedError",
                    text := "Unknown identifier `Old.f`" },
    decl := some s!"{m}.f", region := some .body, declStart := some 0, start := 10, stop := 15 }

def cand (tokens : List String) : Candidate :=
  { rule := "alias", entrenchment := .derived, target := .aliasRename "Old.f" "New.f",
    start := 10, stop := 15, replacement := "New.f", tokens }

def statuses (a b : ModStatus) : Statuses := fun n =>
  if n = "A" then a else if n = "B" then b else .built

def tour : List (String × RunObs) :=
  let mods := [⟨"A", []⟩, ⟨"B", ["A"]⟩]
  [ ("baselined", .baseline ⟨tc "v4.29.0", ["A", "B"], [declA "b1", declB], []⟩ []),
    ("built", .bumped mods ⟨[("Old.f", "Mid.f"), ("Mid.f", "New.f")]⟩),
    ("built", .build (statuses .failing .blocked)),
    ("mending", .diagnosed "A" 1 [⟨site "A", [cand ["sorry"], cand ["New.f", "("], cand ["New.f", "unused"], cand ["New.f"]]⟩]),
    -- the first candidate adds `sorry`: the core rejects it even though the error count fell
    ("mending", .mend (.rebuilt 0 0 [] [])),
    ("mending", .mend .unparsable),
    -- the error count fell, but the candidate caused a linter warning: reject
    ("mending", .mend (.rebuilt 0 1 [] [])),
    ("mending", .mend (.rebuilt 0 0 [] [])),
    ("built", .mended),
    ("built", .build (statuses .built .failing)),
    ("mending", .diagnosed "B" 1 [⟨site "B", []⟩]),
    ("mending", .mend .gaveUp),
    ("built", .mended),
    -- `A.f` is a `def` whose body changed: a Behavior card
    ("awaiting", .certificate ⟨tc "v4.33.1", ["A"], [declA "b1'"], []⟩),
    ("done", .judgment { card := "c-1", kind := .behavior, subject := "A.f",
                         answer := .accept, author := "tour", at_ := "t0" }) ]

namespace Tour

/-- Regression (EVMLean, Ethereum/Wheels.lean): after a site becomes residue,
a candidate at the next site that lowers the module's whole error count from
2 to 1 is accepted. The first version compared 1 with the unresolved count
(1) and rejected it. -/
def residueThenAccept : IO Nat := do
  let m : Mending :=
    { module := "W", errors := 2, decls := 1,
      sites := [⟨site "W", []⟩, ⟨site "W", [cand ["New.f"]]⟩],
      residue := [], accepted := [], wf := by decide, bounded := by decide, sorted := by decide }
  let r := do
    let m ← m.step .gaveUp
    m.step (.rebuilt 1 0 [] [])
  match r with
  | .ok m' =>
    let ok := m'.accepted.length == 1 && m'.errors == 0 && m'.residue.length == 1
    IO.println s!"{if ok then "ok  " else "FAIL"} residue, then accept on the whole error count"
    return if ok then 0 else 1
  | .error e =>
    IO.println s!"FAIL residue, then accept: {repr e}"; return 1

def run : IO Nat := do
  let mut s := RunState.idle "target"
  let mut failed := 0
  for (want, o) in tour do
    s := s.step o
    let ok := s.tag == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {s.tag} (want {want})"
    unless ok do failed := failed + 1
  match s with
  | .done _ _ residue _ =>
    IO.println s!"residue: {residue}"
    unless residue == ["B"] do failed := failed + 1
  | _ => failed := failed + 1
  return failed + (← residueThenAccept)

end Tour
