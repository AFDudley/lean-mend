import LeanMend.Shell.Parse

/-!
`Parse.axiomSet`: the axiom set `compare` sees. Generated `native_decide`
axioms differ in name between toolchains (EquiVM's certificates have them), so
they collapse to one name; order and duplicates do not count.
-/

namespace ParseTest

open LeanMend

def cases : List (List String × List String) :=
  [ (["propext", "Classical.choice", "propext"], ["Classical.choice", "propext"]),
    (["Quot.sound", "Ballot.ok._native.native_decide.ax_1_12",
      "Ballot.ok._native.native_decide.ax_1_15"], ["Quot.sound", "native_decide"]),
    (["Foo.ax_1_2"], ["Foo.ax_1_2"]) ]

def run : IO Nat := do
  let mut failed := 0
  for (raw, want) in cases do
    let got := Parse.axiomSet raw
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} axiomSet {raw} = {got}"
    unless ok do failed := failed + 1
  return failed

end ParseTest
