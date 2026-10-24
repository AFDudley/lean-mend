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
  [ ("baselined", .baseline ⟨tc "v4.29.0", ["A", "B"], [declA "b1", declB]⟩ []),
    ("built", .bumped mods ⟨[("Old.f", "Mid.f"), ("Mid.f", "New.f")]⟩),
    ("built", .build (statuses .failing .blocked)),
    ("mending", .diagnosed "A" [⟨site "A", [cand ["sorry"], cand ["New.f", "("], cand ["New.f"]]⟩]),
    -- the first candidate adds `sorry`: the core rejects it even though the error count fell
    ("mending", .mend (.rebuilt 0 [])),
    ("mending", .mend .unparsable),
    ("mending", .mend (.rebuilt 0 [])),
    ("built", .mended),
    ("built", .build (statuses .built .failing)),
    ("mending", .diagnosed "B" [⟨site "B", []⟩]),
    ("mending", .mend .gaveUp),
    ("built", .mended),
    -- `A.f` is a `def` whose body changed: a Behavior card
    ("awaiting", .certificate ⟨tc "v4.33.1", ["A"], [declA "b1'"]⟩),
    ("done", .judgment { card := "c-1", kind := .behavior, subject := "A.f",
                         answer := .accept, author := "tour", at_ := "t0" }) ]

namespace Tour

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
  return failed

end Tour
