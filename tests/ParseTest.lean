import LeanMend.Shell.Parse
import LeanMend.Shell.Target

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

/-- `Shell.clashModule`: the module the certificate probe moves out of a part.
The probe's error carries the lake command line first, then Lean's message. -/
def clashCases : List (String × Option String) :=
  [ ("lake #[env, lean, --run, .lean-mend/Probe.lean, decls-batch, x.txt] in /t exited 1:\n" ++
      "uncaught exception: import Examples.ERC20.SpecTests failed, environment already " ++
      "contains 'main' from Tests.DiffTest.Main", some "Examples.ERC20.SpecTests"),
    ("uncaught exception: unknown module prefix 'Imports'", none),
    ("uncaught exception: import Foo failed: object file not found", none) ]

def run : IO Nat := do
  let mut failed := 0
  for (raw, want) in cases do
    let got := Parse.axiomSet raw
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} axiomSet {raw} = {got}"
    unless ok do failed := failed + 1
  for (err, want) in clashCases do
    let got := Shell.clashModule err
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} clashModule = {got}"
    unless ok do failed := failed + 1
  return failed

end ParseTest
