import LeanMend.Core.Ops
import LeanMend.Shell.Parse
import LeanMend.Shell.Target

/-!
Edit operations on one tactic node (`docs/rules.md` § Edit operations), and the
rule loader's refusals. Each node is built from its text: tokens are the
whitespace-separated words, with `[`, `]` and `,` split out, at their byte
offsets, as the probe's `node` reports them.
-/

namespace OpsTest

open LeanMend

/-- A node at offset 100 whose tokens are the words of `text`. -/
def node (text : String) : Node :=
  let spaced := (text.replace "[" " [ ").replace "]" " ] " |>.replace "," " , "
  let words := (spaced.splitOn " ").filter (· ≠ "")
  -- the byte offset of each word, searching left to right
  let (toks, _) := words.foldl (init := (([] : List Token), 0)) fun (acc, from_) w =>
    let rest := String.fromUTF8! (text.toUTF8.extract from_ text.utf8ByteSize)
    let i := ((rest.splitOn w).head!).utf8ByteSize + from_
    (acc ++ [{ text := w, start := 100 + i, stop := 100 + i + w.utf8ByteSize }], i + w.utf8ByteSize)
  { kind := "Lean.Parser.Tactic.test", start := 100, stop := 100 + text.utf8ByteSize, text,
    column := 4, tokens := toks }

def cases : List (String × EditOp × String × Option String) :=
  [ ("add to a list", .simpArgAdd "foo", "simp [a, b]", some "simp [a, b, foo]"),
    ("add to an empty list", .simpArgAdd "foo", "simp []", some "simp [foo]"),
    ("add after only", .simpArgAdd "foo", "simp only at h", some "simp only [foo] at h"),
    ("add with no list", .simpArgAdd "foo", "simpa using h", some "simpa [foo] using h"),
    ("already present: no candidate", .simpArgAdd "a", "simp [a]", none),
    ("simpa to exact", .simpaToExact, "simpa [x, y] using h z", some "exact h z"),
    ("simpa without using: no candidate", .simpaToExact, "simpa [x]", none),
    ("not simpa: no candidate", .simpaToExact, "simp [x]", none),
    ("rw to erw", .keywordSwap "rw" "erw", "rw [h] at g", some "erw [h] at g"),
    ("keyword mismatch: no candidate", .keywordSwap "rw" "erw", "simp [h]", none),
    ("delete", .deleteTactic, "decide +kernel", some ""),
    ("match on a literal to if", .matchToIf, "match val with | ⟨0⟩ => f val | _ => g val",
      some "if val = ⟨0⟩ then f val\n    else g val"),
    ("a pattern that binds: no candidate", .matchToIf, "match o with | some x => x | _ => 0", none),
    ("three arms: no candidate", .matchToIf, "match n with | 0 => a | 1 => b | _ => c", none),
    ("second arm not _: no candidate", .matchToIf, "match n with | 0 => a | 1 => b", none),
    ("match on numerals to .val", .matchOnVal, "match p with | 1 => a | 2 => b | _ => c",
      some "match p.val with | 1 => a | 2 => b | _ => c"),
    ("a non-numeral pattern: no candidate", .matchOnVal, "match p with | ⟨1⟩ => a | _ => c", none),
    ("append at the node's column", .appendTactic "omega", "simp [a]", some "simp [a]\n    omega") ]

def prefixCases : List (String × Option String) :=
  [ ("Batteries.RBMap", some "RBTree.RBMap"),
    ("Batteries.RBMap.ofList", some "RBTree.RBMap.ofList"),
    ("Batteries.RBMapX", none),
    ("Mathlib.Batteries.RBMap", none) ]

/-- A site in `D.f` whose body `:= by\n  simp\n  simp` starts at byte 50. -/
def bodySite : Site :=
  { diagnostic := { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
                    severity := .error, kind := "Tactic.unsolvedGoals", text := "unsolved goals" },
    decl := some "D.f", region := some .body, declStart := some 40, start := 50, stop := 60,
    body := some (50, ":= by\n  simp\n  simp") }

def replaceRule (old new : String) : Rule :=
  { name := "agent", cls := .unsolvedGoals, entrenchment := .proposed, family := .any,
    ops := [.replaceInBody "D.f" old new] }

/-- `open Batteries (RBMap RBSet)` at byte 200: Lean reports
``unknown constant `Batteries.RBMap` `` at the token `RBMap`. -/
def openNode : Node :=
  { kind := "Lean.Parser.Command.open", start := 200, stop := 228, column := 0,
    text := "open Batteries (RBMap RBSet)",
    tokens := [⟨"open", 200, 204⟩, ⟨"Batteries", 205, 214⟩, ⟨"(", 215, 216⟩,
               ⟨"RBMap", 216, 221⟩, ⟨"RBSet", 222, 227⟩, ⟨")", 227, 228⟩] }

def openSite : Site :=
  { diagnostic := { module := "M", line := 1, column := 16, endLine := 1, endColumn := 21,
                    severity := .error, kind := "[anonymous]",
                    text := "Unknown constant `Batteries.RBMap`" },
    decl := none, region := none, declStart := none, start := 216, stop := 221, text := "RBMap" }

def ruleJson (cls op : String) : String :=
  s!"\{\"name\": \"r\", \"class\": \"{cls}\", \"entrenchment\": \"ratified\", \"node\": \"any\", \"candidates\": [\{\"op\": \"{op}\"}]}"

def run : IO Nat := do
  let mut failed := 0
  for (what, op, text, want) in cases do
    let got := applyOp op (node text)
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {what}: {repr got}"
    unless ok do failed := failed + 1
  for (w, want) in prefixCases do
    let got := swapPrefix "Batteries.RBMap" "RBTree.RBMap" w
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} swapPrefix {w}: {repr got}"
    unless ok do failed := failed + 1
  for (what, old, want) in
      [("unique text in the body: replaced at its byte range", ":= by", some (50, 55, "by omega")),
       ("text that occurs twice: no candidate", "simp", none),
       ("text not in the body: no candidate", "rfl", none)] do
    let got := (ruleCandidates (replaceRule old "by omega") [] bodySite).head?.map
      fun c => (c.start, c.stop, c.replacement)
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} replaceInBody, {what}: {repr got}"
    unless ok do failed := failed + 1
  do
    let r : Rule := { name := "mv", cls := .unknownIdentifier, entrenchment := .proposed,
                      family := .any, ops := [.renamePrefix "Batteries.RBMap" "RBTree.RBMap"] }
    let got := (ruleCandidates r [openNode] openSite).head?.map fun c => (c.start, c.stop, c.replacement)
    let ok := got == some (205, 214, "RBTree")
    IO.println s!"{if ok then "ok  " else "FAIL"} renamePrefix in `open X (n …)` moves X: {repr got}"
    unless ok do failed := failed + 1
  -- Lake does not track the file that `include_str` reads, so a change to
  -- probe/Probe.lean alone leaves the old probe in the binary. Fail loud.
  do
    let ok := LeanMend.Shell.probeSource == (← IO.FS.readFile "probe/Probe.lean")
    IO.println s!"{if ok then "ok  " else "FAIL"} the embedded probe equals probe/Probe.lean{if ok then "" else " (delete .lake/build/**/LeanMend/Shell/Target.* and rebuild)"}"
    unless ok do failed := failed + 1
  for (what, cls, op, accept) in
      [("deleteTactic for noGoals is loaded", "noGoals", "deleteTactic", true),
       ("deleteTactic for typeMismatch is refused", "typeMismatch", "deleteTactic", false),
       ("node any on class unknown is refused", "unknown", "simpaToExact", false)] do
    let r := Lean.Json.parse (ruleJson cls op) >>= Parse.rule
    let ok := r.toBool == accept
    IO.println s!"{if ok then "ok  " else "FAIL"} {what}"
    unless ok do failed := failed + 1
  return failed

end OpsTest
