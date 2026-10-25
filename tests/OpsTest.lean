import LeanMend.Core.Ops
import LeanMend.Shell.Parse
import LeanMend.Shell.Target
import LeanMend.Core.Compare

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
    ("simpa split into simp at h ⊢ and exact h", .simpaSplit, "simpa [sendEth] using hXiAcc",
      some "simp [sendEth] at hXiAcc ⊢\n    exact hXiAcc"),
    ("simpa split, multi-line list", .simpaSplit, "simpa [a,\n  b] using hXi",
      some "simp [a,\n  b] at hXi ⊢\n    exact hXi"),
    ("simpa using a term, not a name: no candidate", .simpaSplit, "simpa [x] using h z", none),
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
  -- Decision D10: a candidate that adds a declaration is not clean.
  for (what, repl, want) in
      [("a helper lemma is refused", "rfl\n@[simp] theorem t : 1 = 1 := rfl", false),
       ("a new def is refused", "0\ndef helper := 1", false),
       ("a have inside a proof is allowed", "by\n  have h : 1 = 1 := rfl\n  omega", true)] do
    let c : Candidate := { rule := "t", entrenchment := .proposed, target := .body "D.f",
                           start := 0, stop := 0, replacement := repl, tokens := replacementTokens repl }
    let ok := c.clean == want
    IO.println s!"{if ok then "ok  " else "FAIL"} D10: {what}"
    unless ok do failed := failed + 1
  for (t, want) in [("| unchanged {σ σ'}:", some "| unchanged {σ σ' : _}:"),
                    ("| f (a b) {c} : T", some "| f (a b : _) {c : _} : T"),
                    -- EVMLean: the application in the constructor's type stays
                    ("| call_prelude {σ r s v z}:\n    acc σ (sendEth r s v z σ)",
                      some "| call_prelude {σ r s v z : _}:\n    acc σ (sendEth r s v z σ)"),
                    ("| c (x : Nat) {y}: R (f x y)", some "| c (x : Nat) {y : _}: R (f x y)"),
                    ("{σ : AccountMap}", none), ("{ x := 1 }", none), ("{x | p x}", none),
                    ("σ", none), ("{}", none)] do
    let got := annotateBinders t
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} annotateBinders {t}: {repr got}"
    unless ok do failed := failed + 1
  do
    let txt := "inductive c (acc : A) : M → M → Prop where\n  | unchanged {σ σ'}:\n    u acc σ σ'"
    let site : Site :=
      { diagnostic := { module := "M", line := 2, column := 15, endLine := 2, endColumn := 16,
                        severity := .error, kind := "[anonymous]",
                        text := "Only parameters appearing in the declaration header may have their binders kinds be overridden" },
        decl := some "c", region := some .statement, declStart := some 0, start := 60, stop := 61,
        statement := some (0, txt) }
    let ok := match typeCandidates site with
      | [c] => c.clean && c.replacement.contains ':' && (c.target matches .typeAnnotation _)
      | _ => false
    IO.println s!"{if ok then "ok  " else "FAIL"} D11: the narrowing of a whole inductive is clean (it adds no declaration)"
    unless ok do failed := failed + 1
  -- Decision D11: a changed type is a warning from typeChanges, and compare
  -- (which blocks `done`) ignores it.
  do
    let ty (h : String) : Decl := { name := "T", module := "M", kind := .inductive,
                                    statementHash := h, bodyHash := "", axioms := [] }
    let base : Certificate := { toolchain := ⟨"a"⟩, built := ["M"], decls := [ty "h1"] }
    let after : Certificate := { toolchain := ⟨"b"⟩, built := ["M"], decls := [ty "h2"] }
    let ok := (typeChanges ⟨[]⟩ base after).map (·.2) == ["changed"] && (compare ⟨[]⟩ base after []).isEmpty
    IO.println s!"{if ok then "ok  " else "FAIL"} a changed type is a warning, not a finding"
    unless ok do failed := failed + 1
  -- The file-wide namespace move: every occurrence in one edit, and a site of
  -- class `unknown` that names a moved name triggers it.
  do
    let src := "def f (s : Batteries.RBNode.Stream α) := s\n| Batteries.RBNode.Stream.nil => Batteries.RBNode.all₂ x"
    let site : Site :=
      { diagnostic := { module := "M", line := 2, column := 2, endLine := 2, endColumn := 10,
                        severity := .error, kind := "[anonymous]",
                        text := "Invalid pattern variable: Variable name must be atomic, but `Batteries.RBNode.Stream.nil` has multiple components" },
        decl := some "f", region := some .body, declStart := some 0, start := 47, stop := 74,
        text := "Batteries.RBNode.Stream.nil", file := src }
    let r : Rule := { name := "mv", cls := .unknownIdentifier, entrenchment := .proposed,
                      family := .any, ops := [.renamePrefix "Batteries.RBNode" "RBTree.RBNode"] }
    let ok := match ruleCandidates r [] site with
      | [c] => c.start == 0 && c.replacement ==
          "def f (s : RBTree.RBNode.Stream α) := s\n| RBTree.RBNode.Stream.nil => RBTree.RBNode.all₂ x"
          && c.changed.length == 3 && c.clean
      | _ => false
    IO.println s!"{if ok then "ok  " else "FAIL"} renamePrefix renames all 3 occurrences in one edit, from an `unknown`-class site"
    unless ok do failed := failed + 1
  -- valCompare: the class of `match x with` over numerals, declaration-wide.
  for (what, src, want) in
      [("EVMLean precompile_dispatch_match_eq_if (match, if, have)",
        "(match p with\n  | 1 => a1 | _ => d) =\n  (if p = 1 then a1 else d) := by\n  have h1 : p ≠ 1 := by assumption",
        some "(match p.val with\n  | 1 => a1 | _ => d) =\n  (if p.val = 1 then a1 else d) := by\n  have h1 : p.val ≠ 1 := by assumption"),
       ("another variable and a non-numeral comparison stay",
        "if q = 1 then a else if p = q then b else if p = 2 then c else d",
        some "if q = 1 then a else if p = q then b else if p.val = 2 then c else d"),
       ("p == 1 and p.val = 1 stay", "if p == 1 then a else if p.val = 1 then b else c", none)] do
    let got := (valOfLiterals "p" src).map (·.1)
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} valOfLiterals, {what}"
    unless ok do failed := failed + 1
  do
    let d : Diagnostic :=
      { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
        severity := .error, kind := "[anonymous]",
        text := "failed to synthesize\n  Decidable (p✝ = 1)\n\nHint: Additional diagnostic" }
    let ok := decidableVar d == some "p"
    IO.println ((if ok then "ok  " else "FAIL") ++ " decidableVar reads p from Decidable (p✝ = 1)")
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
