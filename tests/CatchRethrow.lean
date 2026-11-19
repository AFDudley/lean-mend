import Lean

/-!
Law LM5 (`docs/laws.md`, no silent omission): a step that cannot compute a
result for an item stops and names the item; no catch replaces a result.

Fails if a `catch` branch in a `.lean` file under `LeanMend/`, `probe/` or
`Main.lean` has no `throw`. The branch is the text after the `catch` keyword
on its own line, plus each following line that is indented more than that
line. A branch that matches on the error and rethrows the other cases
(`| .alreadyExists .. => pure false | e => throw e`) has a `throw`, so it
passes. Text in a `--` line comment is not code.

The gate runs it with `lake env lean tests/CatchRethrow.lean`. stdout carries
one JSON object (docs/process.md § Check scripts):
`{"runner": "CatchRethrow", "checked": N, "findings": [{"file", "line", "text"}]}`,
where `checked` is the number of `catch` branches read.
-/

open Lean

/-- `s` with any `--` line comment removed. -/
def codeOf (s : String) : String := (s.splitOn "--").headD ""

/-- `text` with each `/- … -/` block comment (nested ones too) replaced by
spaces, its line breaks kept, so line numbers do not change. -/
def withoutBlockComments (text : String) : String := Id.run do
  let cs := text.toList.toArray
  let mut out : Array Char := #[]
  let mut depth := 0
  let mut i := 0
  while i < cs.size do
    let c := cs[i]!
    let next := cs[i + 1]?
    if c == '/' && next == some '-' then
      depth := depth + 1; out := out.push ' ' |>.push ' '; i := i + 2
    else if depth > 0 && c == '-' && next == some '/' then
      depth := depth - 1; out := out.push ' ' |>.push ' '; i := i + 2
    else
      out := out.push (if depth > 0 && c != '\n' then ' ' else c); i := i + 1
  pure (String.ofList out.toList)


def indentOf (s : String) : Nat := (s.toList.takeWhile (· == ' ')).length

/-- Whether `s` holds `kw` as a whole word. -/
def hasWord (s kw : String) : Bool :=
  let isId (c : Char) := c.isAlphanum || c == '_' || c == '.' || c == '\''
  let parts := s.splitOn kw
  (List.range (parts.length - 1)).any fun i =>
    let before := parts[i]!
    let after := parts[i + 1]!
    !(before.toList.getLast?.map isId).getD false && !(after.toList.head?.map isId).getD false

/-- The findings of one file: each `catch` line whose branch has no `throw`. -/
def fileFindings (path : String) (text : String) : Nat × Array Json := Id.run do
  let lines := ((withoutBlockComments text).splitOn "\n").toArray
  let mut checked := 0
  let mut out : Array Json := #[]
  for i in [0:lines.size] do
    let code := codeOf lines[i]!
    unless hasWord code "catch" do continue
    checked := checked + 1
    let ind := indentOf lines[i]!
    let mut branch := ((code.splitOn "catch").drop 1).foldl (· ++ ·) ""
    let mut j := i + 1
    while j < lines.size && (lines[j]!.trimAscii.isEmpty || indentOf lines[j]! > ind) do
      branch := branch ++ "\n" ++ codeOf lines[j]!
      j := j + 1
    unless hasWord branch "throw" do
      out := out.push (Json.mkObj [("file", toJson path), ("line", toJson (i + 1)),
        ("text", toJson lines[i]!.trimAscii.toString)])
  pure (checked, out)

partial def leanFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut acc := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then acc := acc ++ (← leanFiles e.path)
    else if e.path.extension == some "lean" then acc := acc.push e.path
  pure acc

run_cmd do
  let files := (← leanFiles "LeanMend") ++ (← leanFiles "probe") ++ #[("Main.lean" : System.FilePath)]
  let mut checked := 0
  let mut findings : Array Json := #[]
  for f in files.qsort (·.toString < ·.toString) do
    let (n, fs) := fileFindings f.toString (← IO.FS.readFile f)
    checked := checked + n
    findings := findings ++ fs
  IO.println (Json.mkObj [("runner", "CatchRethrow"), ("checked", toJson checked),
    ("findings", Json.arr findings)]).compress
  unless findings.isEmpty do
    throwError "{findings.size} catch branch(es) replace a result with no throw (law LM5)"
