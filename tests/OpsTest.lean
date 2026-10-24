import LeanMend.Core.Ops
import LeanMend.Shell.Parse

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
  { kind := "Lean.Parser.Tactic.test", start := 100, stop := 100 + text.utf8ByteSize, text, tokens := toks }

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
    ("delete", .deleteTactic, "decide +kernel", some "") ]

def ruleJson (cls op : String) : String :=
  s!"\{\"name\": \"r\", \"class\": \"{cls}\", \"entrenchment\": \"ratified\", \"node\": \"any\", \"candidates\": [\{\"op\": \"{op}\"}]}"

def run : IO Nat := do
  let mut failed := 0
  for (what, op, text, want) in cases do
    let got := applyOp op (node text)
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} {what}: {repr got}"
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
