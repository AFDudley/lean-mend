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
  -- The /proc parsers of the memory limit (docs/parallel.md P24), on text
  -- captured on kelce on 2026-11-05 from EquiVM run 7: a probe `lean`
  -- process (pid 2756208) and its `lake env` parent (pid 2755994).
  let leanStatus := "Name:\tlean\nPid:\t2756208\nPPid:\t2755994\nVmRSS:\t 5936592 kB\n" ++
    "RssAnon:\t 5559704 kB\nRssFile:\t  376888 kB\nRssShmem:\t       0 kB\n"
  let lakeStat := "2755994 (lake) S 2674559 2674559 2674559 0 -1 4194304 40358 5491 59 0 39 123"
  let meminfo := "MemTotal:       196946700 kB\nMemFree:        32059484 kB\nMemAvailable:   34480068 kB\n"
  for (what, ok) in
      [("privateRss: RssAnon plus RssShmem of a probe lean, not RssFile",
        (Parse.privateRss leanStatus).toOption == some ⟨5559704⟩),
       ("privateRss: a kernel thread has no Rss line and holds 0",
        (Parse.privateRss "Name:\tkthreadd\nPid:\t2\n").toOption == some ⟨0⟩),
       ("statParent: the parent of the probe's lake process is the driver",
        (Parse.statParent lakeStat).toOption == some 2674559),
       ("statParent: a command name with spaces and a parenthesis",
        (Parse.statParent "7 (a b) c) S 42 7 7").toOption == some 42),
       ("memAvailable: the MemAvailable line", (Parse.memAvailable meminfo).toOption == some ⟨34480068⟩),
       ("memAvailable: a text with no MemAvailable line is an error",
        (Parse.memAvailable "MemTotal: 1 kB\n").toOption.isNone)] do
    IO.println s!"{if ok then "ok  " else "FAIL"} {what}"
    unless ok do failed := failed + 1
  -- `Parse.declLine`: the probe's `unread` line becomes the typed
  -- `DeclUnread` (docs/verification.md § The certificate); a row stays a row.
  let line (s : String) := (Lean.Json.parse s).toOption.getD .null
  let unread := line
    "{\"name\":\"App.local_sum\",\"module\":\"App.T\",\"unread\":\"no command that parsed holds byte 9\"}"
  let row := line ("{\"name\":\"App.t\",\"module\":\"App.T\",\"kind\":\"theorem\"," ++
    "\"statementTokens\":[\":\",\"True\"],\"body\":\":= trivial\",\"axioms\":[]}")
  for (what, ok) in
      [("declLine: an unread line is DeclUnread with its module, declaration and reason",
        match Parse.declLine id unread with
        | .ok (.error x) => x == { module := "App.T", decl := "App.local_sum",
                                   reason := "no command that parsed holds byte 9" }
        | _ => false),
       ("declLine: a row is a Decl",
        match Parse.declLine id row with
        | .ok (.ok d) => d.name == "App.t" && d.module == "App.T"
        | _ => false)] do
    IO.println s!"{if ok then "ok  " else "FAIL"} {what}"
    unless ok do failed := failed + 1
  return failed

end ParseTest
