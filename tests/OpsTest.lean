import LeanMend.Core.Ops
import LeanMend.Shell.Parse
import LeanMend.Shell.Target
import LeanMend.Core.Compare
import LeanMend.Core.Mend
import LeanMend.Core.Run

/-!
Edit operations on one tactic node (`docs/rules.md` § Edit operations), and the
rule loader's refusals. Each node is built from its text: tokens are the
whitespace-separated words, with `[`, `]` and `,` split out, at their byte
offsets, as the probe's `node` reports them.
-/

namespace OpsTest

open LeanMend

-- `decide` evaluates `Mending.sorted` over test sites with 300-byte
-- declaration texts; the default recursion depth is too small for that.
set_option maxRecDepth 20000

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
    ("simpa using a term: named by have, then split", .simpaSplit,
      "simpa [σ₁] using trans hσ₁\n      (debit σ₁ s v)",
      some "have := trans hσ₁\n      (debit σ₁ s v)\n    simp [σ₁] at this ⊢\n    exact this"),
    ("simpa using a projection: named by have, then split", .simpaSplit,
      "simpa only [u256_add_assoc] using hwf.d3",
      some "have := hwf.d3\n    simp only [u256_add_assoc] at this ⊢\n    exact this"),
    ("simpa using to using!: the close at default transparency", .simpaUsingBang,
      "simpa only [u256_add_assoc] using hwf.d3", some "simpa only [u256_add_assoc] using! hwf.d3"),
    ("simpa without using: no using! candidate", .simpaUsingBang, "simpa [x]", none),
    ("simpa already with using!: no candidate", .simpaUsingBang, "simpa [x] using! h", none),
    ("not simpa: no using! candidate", .simpaUsingBang, "simp [x] at h", none),
    ("simpa with nothing after using: no candidate", .simpaSplit, "simpa [x] using", none),
    ("not simpa: no candidate", .simpaToExact, "simp [x]", none),
    ("rw to erw", .keywordSwap "rw" "erw", "rw [h] at g", some "erw [h] at g"),
    ("keyword mismatch: no candidate", .keywordSwap "rw" "erw", "simp [h]", none),
    ("delete", .deleteTactic, "decide +kernel", some ""),
    ("a rw of one show term is deleted", .deleteShowRewrite,
      "rw [show (⟨32⟩ : W).toNat = 32 by native_decide]", some ""),
    ("a rw of two show terms, at a hypothesis, is deleted", .deleteShowRewrite,
      "rw [show a = b by rfl, show f [c, d] = e from h] at g", some ""),
    ("a rw with a lemma after the show: no candidate", .deleteShowRewrite,
      "rw [show a = b by rfl, h]", none),
    ("a rw of a lemma: no candidate", .deleteShowRewrite, "rw [if_neg]", none),
    ("rwa also closes the goal: no candidate", .deleteShowRewrite, "rwa [show a = b by rfl]", none),
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

/-- S3a (docs/parallel.md § Level 2: parallel frontier modules): one open
site, named `m`, with no candidate — enough to drive a `Mending` straight
to `gaveUp`. -/
def fleetSite (m : String) : Site :=
  { diagnostic := { module := m, line := 1, column := 0, endLine := 1, endColumn := 1,
                    severity := .error, kind := "[anonymous]", text := "e" },
    decl := some s!"{m}.f", region := some .body, declStart := some 0, start := 10, stop := 20 }

/-- A `Mending` for module `m`, with one open site and no candidate. -/
def fleetMending (m : String) : Mending :=
  { module := m, errors := 1, decls := 1, sites := [⟨fleetSite m, []⟩],
    residue := [], accepted := [], wf := by simp [fleetSite], bounded := by simp [fleetSite],
    sorted := by simp [fleetSite] }

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
    let got := (ruleCandidates false (replaceRule old "by omega") [] bodySite).head?.map
      fun c => (c.start, c.stop, c.replacement)
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} replaceInBody, {what}: {repr got}"
    unless ok do failed := failed + 1
  do
    let r : Rule := { name := "mv", cls := .unknownIdentifier, entrenchment := .proposed,
                      family := .any, ops := [.renamePrefix "Batteries.RBMap" "RBTree.RBMap"] }
    let got := (ruleCandidates false r [openNode] openSite).head?.map fun c => (c.start, c.stop, c.replacement)
    let ok := got == some (205, 214, "RBTree")
    IO.println s!"{if ok then "ok  " else "FAIL"} renamePrefix in `open X (n …)` moves X: {repr got}"
    unless ok do failed := failed + 1
  -- Lake does not track the file that `include_str` reads, so a change to
  -- probe/Probe.lean alone leaves the old probe in the binary. Fail loud.
  do
    let ok := LeanMend.Shell.probeSource == (← IO.FS.readFile "probe/Probe.lean")
    IO.println s!"{if ok then "ok  " else "FAIL"} the embedded probe equals probe/Probe.lean{if ok then "" else " (delete .lake/build/**/LeanMend/Shell/Target.* and rebuild)"}"
    unless ok do failed := failed + 1
  -- A probe process that reads a request and exits with no reply (EquiVM
  -- run 5): the request reaps it and throws its own error. The stop after
  -- it must not wait again: a second wait fails with ECHILD ("no such
  -- thing"), and that error replaced the request's error.
  do
    let child ← IO.Process.spawn
      { cmd := "sh", args := #["-c", "read l; echo gone >&2; exit 3"],
        stdin := .piped, stdout := .piped, stderr := .piped }
    let s ← LeanMend.Shell.ProbeSession.ofChild child LeanMend.probeCap
    let got ← try
        try
          discard <| LeanMend.Shell.probeServeRequest s "F.lean" (Lean.Json.mkObj [("op", Lean.toJson "syntax")])
          pure "a reply"
        finally LeanMend.Shell.probeServeStop s
      catch e => pure (toString e)
    let ok := got == "probe serve: process exited 3 with no reply for F.lean; its stderr:\ngone\n"
    IO.println s!"{if ok then "ok  " else "FAIL"} probeServeStop after a probe that exited keeps the request's error: {got}"
    unless ok do failed := failed + 1
  -- docs/parallel.md P24: a probe that Lean stopped at its `lean -M` cap
  -- (the text of v4.29.0, v4.33.1 and v4.35.0, measured on kelce on
  -- 2026-11-06) sets `overCap`, so the driver stops the run with the typed
  -- `CapExceeded`.
  do
    let child ← IO.Process.spawn
      { cmd := "sh", args := #["-c", "read l; echo \"excessive memory consumption detected at 'interpreter' (potential solution: increase memory consumption threshold)\" >&2; exit 1"],
        stdin := .piped, stdout := .piped, stderr := .piped }
    let s ← LeanMend.Shell.ProbeSession.ofChild child LeanMend.probeCap
    try
      try discard <| LeanMend.Shell.probeServeRequest s "F.lean" (Lean.Json.mkObj [("op", Lean.toJson "syntax")])
      finally LeanMend.Shell.probeServeStop s
    catch _ => pure ()
    let ok ← s.overCap.get
    IO.println s!"{if ok then "ok  " else "FAIL"} a probe that Lean stopped at its cap sets overCap"
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
  -- The clean check reads the tokens that the edit adds, not every token of the
  -- replacement (docs/machine.md, structural check 2). EquiVM run 5,
  -- Tests/Pipeline/Vault/Dispatch.lean 270: the node already holds
  -- `native_decide`, and `simpaToExact` keeps it. Run 5 rejected the edit.
  do
    let text := "simpa [w] using (show p by rw [h]; native_decide)"
    let n := node text
    let site : Site :=
      { diagnostic := { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
                        severity := .error, kind := "[anonymous]",
                        text := "Type mismatch: After simplification, term" },
        decl := some "D.f", region := some .body, declStart := some 0, start := 100,
        stop := 100 + text.utf8ByteSize, file := String.ofList (List.replicate 100 ' ') ++ text }
    let r : Rule := { name := "r", cls := .typeMismatch, entrenchment := .proposed, family := .simp,
                      ops := [.simpaToExact, .appendTactic "native_decide"] }
    let got := (ruleCandidates false r [n] site).map fun c => ((c.replacement.take 5).toString, c.clean)
    let ok := got == [("exact", true), ("simpa", false)]
    IO.println s!"{if ok then "ok  " else "FAIL"} D10: a kept native_decide is clean, an added one is not: {repr got}"
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
    let ok := match ruleCandidates false r [] site with
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
  -- D12 combined candidate (X7, docs/parallel.md § The D12 combined
  -- candidate): a declaration whose body has the valCompare pattern and
  -- whose statement has it too gives one `followStatement` candidate under
  -- --follow-definition-changes, spanning the whole declaration, and none
  -- without the flag.
  do
    let full := "(match p with\n  | 1 => a1 | _ => d) =\n  (if p = 1 then a1 else d) := by\n  have h1 : p ≠ 1 := by assumption"
    let stmt := "(match p with\n  | 1 => a1 | _ => d) =\n  (if p = 1 then a1 else d)"
    let wantRepl := "(match p.val with\n  | 1 => a1 | _ => d) =\n  (if p.val = 1 then a1 else d) := by\n  have h1 : p.val ≠ 1 := by assumption"
    let d : Diagnostic := { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
                            severity := .error, kind := "[anonymous]",
                            text := "failed to synthesize\n  Decidable (p✝ = 1)" }
    let site : Site := { diagnostic := d, decl := some "D.f", region := some .body,
                         declStart := some 1000, start := 1001, stop := 1010,
                         declText := some (1000, full), statement := some (1000, stmt) }
    let r : Rule := { name := "match-literal", cls := .missingDecidable, entrenchment := .proposed,
                      family := .any, ops := [.valCompare] }
    let noFollow := ruleCandidates false r [] site
    let got := ruleCandidates true r [] site
    let ok := noFollow.isEmpty &&
      match got with
      | [c] => c.target matches .followStatement "D.f" &&
          c.start == 1000 && c.stop == 1000 + full.utf8ByteSize &&
          c.replacement == wantRepl && c.changed.length == 3
      | _ => false
    IO.println s!"{if ok then "ok  " else "FAIL"} D12: a valCompare body edit and its statement follow are one candidate"
    unless ok do failed := failed + 1
  do
    let d : Diagnostic :=
      { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
        severity := .error, kind := "[anonymous]",
        text := "failed to synthesize\n  Decidable (p✝ = 1)\n\nHint: Additional diagnostic" }
    let ok := decidableVar d == some "p"
    IO.println ((if ok then "ok  " else "FAIL") ++ " decidableVar reads p from Decidable (p✝ = 1)")
    unless ok do failed := failed + 1
  -- Lean's hint for an unused simp argument, applied (dropSimpArgs).
  for (what, repl, args, want) in
      [("EVMLean AccountLocality 2658",
        "simp [getD_eq, ← get?_eq, ha,\n  hstorage_bne, hstorage_ne_default] at hXi ⊢\n  exact hXi",
        ["hstorage_bne"],
        some "simp [getD_eq, ← get?_eq, ha,\n  hstorage_ne_default] at hXi ⊢\n  exact hXi"),
       ("the first item", "simp [Nat.add_zero, Dep.foo_eq]", ["Nat.add_zero"], some "simp [Dep.foo_eq]"),
       ("the only item: the list goes", "simp only [a] at h", ["a"], some "simp only at h"),
       ("a ← item by its name", "simp [← h, k]", ["h"], some "simp [k]"),
       ("an argument not in the list: none", "simp [a, b]", ["c"], none)] do
    let got := dropSimpArgs repl args
    let ok := got == want
    IO.println s!"{if ok then "ok  " else "FAIL"} dropSimpArgs, {what}: {repr got}"
    unless ok do failed := failed + 1
  -- The Core step: a candidate that clears the error but leaves one unused
  -- simp argument is not accepted; its cleaned form replaces it.
  do
    let c : Candidate := { rule := "r", entrenchment := .proposed, target := .body "D.f",
                           start := 0, stop := 10, replacement := "simp [a, b] at h ⊢", tokens := ["simp", "a", "b", "h"] }
    let site : Site := { diagnostic := { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
                                         severity := .error, kind := "[anonymous]", text := "t" },
                         decl := some "D.f", region := some .body, declStart := some 0, start := 0, stop := 1 }
    let m : Mending := { module := "M", errors := 1, decls := 1, sites := [⟨site, [c]⟩],
                         residue := [], accepted := [],
                         wf := by decide, bounded := by decide, sorted := by decide }
    let ok : Bool := match m.step (.rebuilt 0 1 ["b"] []) with
      | .ok m' => m'.accepted.isEmpty &&
          ((m'.sites.head?.bind (·.candidates.head?)).map (·.replacement) == some "simp [a] at h ⊢")
      | .error _ => false
    IO.println s!"{if ok then "ok  " else "FAIL"} a flagged candidate is not accepted; Lean's hint replaces it"
    unless ok do failed := failed + 1
  -- X1-X4 (`docs/parallel.md`): the Core sorts open sites by the AST
  -- coordinate (declaration index, then `Site.reach`), not by the shell's
  -- message order, and accepts an edit only when the earliest open position
  -- moves strictly toward the end of the file. `D.f` is declaration 1 of 2;
  -- `D.a` is the earlier declaration 0 (EVMLean Semantics 1040 and 288).
  do
    let c : Candidate := { rule := "r", entrenchment := .proposed, target := .body "D.f",
                           start := 140, stop := 160, replacement := "RBTree.RBSet", tokens := ["RBTree.RBSet"] }
    let mkSite (decl : String) (declIdx start declLen : Nat) : Site :=
      { diagnostic := { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
                        severity := .error, kind := "[anonymous]", text := s!"e{decl}{start}" },
        decl := some decl, region := some .body, declStart := some 100,
        declText := some (100, String.ofList (List.replicate declLen 'x')), start, stop := start + 1,
        declIndex := declIdx }
    let head := mkSite "D.f" 1 150 300
    let m : Mending := { module := "M", errors := 1, decls := 3, sites := [⟨head, [c]⟩],
                         residue := [], accepted := [],
                         wf := by decide, bounded := by decide, sorted := by decide }
    for (what, e, s', accept, headStart) in
        [("a later error in the same declaration is exposed: accept", 1,
          [mkSite "D.f" 1 200 292], true, 200),
         ("any number of later errors in the same declaration is exposed: accept", 2,
          [mkSite "D.f" 1 200 292, mkSite "D.f" 1 300 292], true, 200),
         ("the shell's message order does not decide the head: accept", 2,
          [mkSite "D.f" 1 300 292, mkSite "D.f" 1 200 292], true, 200),
         ("no progress, the same error persists: reject", 1, [head], false, 150),
         ("an error earlier in the same declaration appears: reject", 2,
          [mkSite "D.f" 1 100 300, head], false, 150),
         ("an error in an earlier declaration appears: reject", 2,
          [mkSite "D.a" 0 20 300, mkSite "D.f" 1 200 292], false, 150),
         -- EVMLean run 21, AccountLocality 2558: `closeBullet "omega"` failed
         -- inside its own bytes [140, 152); the shorter declaration made the
         -- error's reach smaller than the head's.
         ("the new error starts inside the edit's own bytes: reject", 1,
          [mkSite "D.f" 1 145 292], false, 150),
         ("the head's error persists and the declaration got shorter: reject", 1,
          [mkSite "D.f" 1 150 292], false, 150),
         ("a new error appears in a later declaration: reject", 1,
          [mkSite "D.g" 2 20 300], false, 150)] do
      -- Accepted or not is read on its own; the head is checked only on an
      -- accept, where the exposed site becomes the head site.
      let ok : Bool := match m.step (.rebuilt e 0 [] (s'.map (⟨·, []⟩))) with
        | .ok m' =>
          let acc := !m'.accepted.isEmpty
          acc == accept && (!acc || (m'.sites.head?.map (·.site.start)) == some headStart)
        | .error _ => false
      IO.println s!"{if ok then "ok  " else "FAIL"} exposure: {what}"
      unless ok do failed := failed + 1
    -- Two open sites with one failure text: the edit fixes the first one.
    -- The failure still occurs once, but less often than before: accept.
    let twinAt (start declLen : Nat) : Site := { mkSite "D.f" 1 start declLen with diagnostic := head.diagnostic }
    let m2 : Mending := { module := "M", errors := 2, decls := 3,
                          sites := [⟨head, [c]⟩, ⟨twinAt 250 300, []⟩], residue := [], accepted := [],
                          wf := by decide, bounded := by decide, sorted := by decide }
    let got2 : Bool := match m2.step (.rebuilt 1 0 [] [⟨twinAt 242 292, []⟩]) with
      | .ok m' => !m'.accepted.isEmpty && (m'.sites.head?.map (·.site.start)) == some 242
      | .error _ => false
    IO.println s!"{if got2 then "ok  " else "FAIL"} exposure: one of two identical failures is fixed: accept"
    unless got2 do failed := failed + 1
  -- closeBullet: the innermost bullet (`Lean.cdot`) that holds the site, as
  -- the probe reports it at EVMLean GasLemmas 48.
  do
    let n (k : String) (a b : Nat) (txt : String) : Node :=
      { kind := k, start := a, stop := b, column := 4, text := txt, tokens := [] }
    let nodes := [{ n "Lean.Parser.Tactic.split" 1372 1377 "split" with tokens := [⟨"split", 1372, 1377⟩] },
                  n "Lean.Parser.Tactic.«tactic_<;>_»" 1372 1387 "split <;> omega",
                  n "Lean.cdot" 1369 1387 "· split <;> omega",
                  n "null" 1219 1442 ""]
    let site : Site :=
      { diagnostic := { module := "M", line := 48, column := 6, endLine := 48, endColumn := 11,
                        severity := .error, kind := "[anonymous]",
                        text := "Tactic `split` failed: Could not split an `if` or `match` expression in the goal" },
        decl := some "Ccallgas_lt_Ccall", region := some .body, declStart := some 1000,
        start := 1372, stop := 1377 }
    let r : Rule := { name := "closer", cls := .tacticFailed, entrenchment := .proposed, family := .any,
                      ops := [.closeBullet "omega", .closeBullet "simp_all"] }
    let got := (ruleCandidates false r nodes site).map fun c => (c.start, c.stop, c.replacement)
    let ok := got == [(1369, 1387, "· omega"), (1369, 1387, "· simp_all")]
    IO.println s!"{if ok then "ok  " else "FAIL"} closeBullet replaces the innermost bullet, in rule order: {repr got}"
    unless ok do failed := failed + 1
    -- a closer rule runs after every other rule of its entrenchment
    let other : Rule := { name := "a-other", cls := .tacticFailed, entrenchment := .proposed, family := .any,
                          ops := [.deleteTactic] }
    let order := (proposeAll ⟨[]⟩ [r, other] nodes false false [] site).map (·.replacement)
    let ok2 := order == ["", "· omega", "· simp_all"]
    IO.println s!"{if ok2 then "ok  " else "FAIL"} a closer rule runs last: {repr order}"
    unless ok2 do failed := failed + 1
    -- a rule that only raises maxHeartbeats runs after the closer rule
    let hb : Rule := { name := "a-budget", cls := .tacticFailed, entrenchment := .proposed,
                       family := .any, ops := [.heartbeats 400000] }
    let order3 := (proposeAll ⟨[]⟩ [hb, r, other] nodes false false [] site).map (·.replacement)
    let ok3 := order3 == ["", "· omega", "· simp_all", "set_option maxHeartbeats 400000 in\n"]
    IO.println s!"{if ok3 then "ok  " else "FAIL"} a heartbeats rule runs after every other rule: {repr order3}"
    unless ok3 do failed := failed + 1
  -- simpArgAddPrior: the simp before the site's own tactic, in the indented
  -- sequence that holds the site (EquiVM TransientPackedStorage 59: `simp
  -- only […, Option.bind]`, then `congr 2`, then `apply u256_inj` fails).
  do
    -- an indented sequence at byte 100, column 2; tokens as the probe reports them
    let seq (text : String) : Node :=
      let words := node (text.replace "\n" " ")
      { words with kind := "Lean.Parser.Tactic.tacticSeq1Indented", text := text, column := 2 }
    let at_ (text word : String) : Nat := 100 + ((text.splitOn word).head!).utf8ByteSize
    let siteAt (a : Nat) : Site :=
      { diagnostic := { module := "M", line := 1, column := 0, endLine := 1, endColumn := 1,
                        severity := .error, kind := "[anonymous]",
                        text := "Tactic `apply` failed: could not unify the conclusion of `Nat.add_comm`" },
        decl := some "D.f", region := some .body, declStart := some 0, start := a, stop := a + 5 }
    let r : Rule := { name := "prior", cls := .tacticFailed, entrenchment := .proposed, family := .any,
                      ops := [.simpArgAddPrior "pure"] }
    let t1 := "unfold store\n  simp only [toWord, bind, Option.bind]\n  congr 1\n  apply Nat.add_comm"
    let t2 := "simp [a]\n  simp only [b]\n  rw [h]"
    let simp1 := "simp only [toWord, bind, Option.bind]"
    for (what, text, word, want) in
        [("the simp two tactics before the site gains the lemma", t1, "apply",
          [(at_ t1 "simp", at_ t1 "simp" + simp1.utf8ByteSize, "simp only [toWord, bind, Option.bind, pure]")]),
         ("no simp before the site: no candidate", t1, "unfold", []),
         ("of two simps, the nearer one", t2, "rw",
          [(at_ t2 "simp only", at_ t2 "simp only" + "simp only [b]".utf8ByteSize, "simp only [b, pure]")])] do
      let s := seq text
      let site := siteAt (at_ text word)
      let own : Node := { kind := "Lean.Parser.Tactic.test", start := site.start, stop := site.stop,
                          text := word, column := 2, tokens := [⟨word, site.start, site.stop⟩] }
      let got := (ruleCandidates false r [own, s] site).map fun c => (c.start, c.stop, c.replacement)
      let ok := got == want
      IO.println s!"{if ok then "ok  " else "FAIL"} simpArgAddPrior, {what}: {repr got}"
      unless ok do failed := failed + 1
  for (what, cls, op, accept) in
      [("deleteTactic for noGoals is loaded", "noGoals", "deleteTactic", true),
       ("deleteTactic for typeMismatch is refused", "typeMismatch", "deleteTactic", false),
       ("deleteShowRewrite for tacticFailed is loaded", "tacticFailed", "deleteShowRewrite", true),
       ("deleteShowRewrite for noGoals is refused", "noGoals", "deleteShowRewrite", false),
       ("node any on class unknown is refused", "unknown", "simpaToExact", false)] do
    let r := Lean.Json.parse (ruleJson cls op) >>= Parse.rule
    let ok := r.toBool == accept
    IO.println s!"{if ok then "ok  " else "FAIL"} {what}"
    unless ok do failed := failed + 1
  -- S3a (docs/parallel.md § Level 2: parallel frontier modules): a fleet of
  -- two Mending states, one per module, reaches the same final state
  -- whichever order their observations arrive in. `Fleet.step` replaces a
  -- member in place by its module name, so the order of the two `mend`
  -- observations below does not change either member's own result.
  do
    let fleet : Fleet := { mendings := [fleetMending "A", fleetMending "B"], distinct := by decide }
    let ctx : Context :=
      { target := "t", base := { toolchain := ⟨"a"⟩, built := [], decls := [] }, mods := [],
        aliases := ⟨[]⟩ }
    let st : Statuses := fun _ => .built
    let base : RunState := .mending ctx st fleet
    let summary (s : RunState) : Option (List (String × Nat × Nat)) :=
      match s with
      | .mending _ _ f => some (f.mendings.map fun m => (m.module, m.errors, m.residue.length))
      | _ => none
    let ab := (base.step (.mend "A" .gaveUp)).step (.mend "B" .gaveUp)
    let ba := (base.step (.mend "B" .gaveUp)).step (.mend "A" .gaveUp)
    let ok := summary ab == summary ba && summary ab == some [("A", 0, 1), ("B", 0, 1)]
    IO.println s!"{if ok then "ok  " else "FAIL"} S3a: a fleet of two Mending states reaches \
      the same final state in either order"
    unless ok do failed := failed + 1
  -- docs/parallel.md P8, P21, P22: the dataflow schedule on a chain A ← B ← C
  -- with an unrelated D. A builds, so B is ready to build; C waits for B.
  -- A `moduleBuild` unblocks only a ready blocked module, to built or
  -- failing, and a module the run mended must build.
  do
    let mods : List Module :=
      [⟨"A", []⟩, ⟨"D", []⟩, ⟨"B", ["A", "Init"]⟩, ⟨"C", ["B"]⟩]
    let ctx : Context :=
      { target := "t", base := { toolchain := ⟨"a"⟩, built := [], decls := [] }, mods,
        aliases := ⟨[]⟩ }
    let st : Statuses := fun n =>
      if n == "B" || n == "C" then .blocked else if n == "D" then .failing else .built
    let statusOf (s : RunState) (n : String) : Option ModStatus :=
      match s with | .built _ st' => some (st' n) | _ => none
    let isHalted (s : RunState) : Bool := match s with | .halted _ => true | _ => false
    let base : RunState := .built ctx st
    for (what, ok) in
        [("ready names the open modules whose imports build, in module order",
          ready mods st == ["D", "B"]),
         ("a ready blocked module takes its build result",
          statusOf (base.step (.moduleBuild "B" .failing)) "B" == some .failing),
         ("a blocked module whose import does not build cannot take a result",
          isHalted (base.step (.moduleBuild "C" .built))),
         ("a build that reports a ready module blocked again halts",
          isHalted (base.step (.moduleBuild "B" .blocked))),
         ("a built module must build",
          statusOf (base.step (.moduleBuild "A" .built)) "A" == some .built &&
          isHalted (base.step (.moduleBuild "A" .failing))),
         ("a failing module takes no module build",
          isHalted (base.step (.moduleBuild "D" .built))),
         ("C becomes ready once B builds",
          ready mods (fun n => if n == "C" then .blocked else if n == "D" then .failing else .built)
            == ["D", "C"]),
         ("importClosure names every module C imports, directly or not, in module order",
          importClosure mods "C" == ["A", "B"] && importClosure mods "D" == [])] do
      IO.println s!"{if ok then "ok  " else "FAIL"} dataflow: {what}"
      unless ok do failed := failed + 1
  -- docs/parallel.md P24: the memory limit of a run. Sizes in KiB:
  -- 10 GiB = 10485760, 15 GiB = 15728640, 16 GiB = 16777216, 21 GiB = 22020096.
  do
    let g (n : Nat) : KiB := KiB.ofGiB n
    let est := workEstimate
    let limit := g 21
    let young : Load := { driver := ⟨100000⟩, tree := ⟨1500000⟩, probes := [some ⟨1300000⟩] }
    let two : Load := { driver := ⟨100000⟩, tree := ⟨3000000⟩, probes := [some ⟨1300000⟩, none] }
    let grown : Load := { driver := ⟨100000⟩, tree := ⟨13000000⟩, probes := [some (g 12)] }
    let build (n : Nat) : Load := { driver := ⟨100000⟩, tree := ⟨2000000⟩, probes := [], others := n }
    for (what, ok) in
        [("one live probe and one new: charged 100000 + 2 * 10485760, measured 1500000 + 9185760 + 10485760",
          young.charged est == ⟨21071520⟩ && young.measured est == ⟨21171520⟩ && admits limit est young),
         ("a third probe does not fit 21 GiB: charged 100000 + 3 * 10485760",
          two.charged est == ⟨31557280⟩ && !admits limit est two),
         ("a probe that grew past its charge stops the next admission by the measured check",
          grown.charged est == ⟨21071520⟩ && grown.measured est == ⟨23485760⟩ && !admits limit est grown),
         ("a running build is charged: one fits beside a new probe, two do not",
          admits limit est (build 1) && !admits limit est (build 2)),
         ("when nothing runs, one item starts even past the limit",
          admits limit est { driver := g 30, tree := g 30, probes := [] }),
         ("the hard cap is the charge times 3/2: 15 GiB, lean -M 15360",
          probeCap == ⟨15728640⟩ && probeCap.toMiB == 15360),
         ("the default limit is MemAvailable minus 16 GiB: 34480068 - 16777216",
          (MemoryLimit.available ⟨34480068⟩).limit == ⟨17702852⟩),
         ("a MemAvailable below the reserve gives the limit 0",
          (MemoryLimit.available ⟨1000⟩).limit == ⟨0⟩),
         ("a round with no extra probe runs every candidate on its module's probe",
          roundPlacement 3 0 == [.own, .own, .own]),
         ("a round uses at most width - 1 extra probes",
          roundPlacement 3 5 == [.own, .nested, .nested]),
         ("a round with one extra probe runs the third candidate on its module's probe",
          roundPlacement 3 1 == [.own, .nested, .own]),
         ("processTree: a process, its child and its grandchild, not a sibling",
          processTree [(10, 1), (11, 10), (12, 11), (13, 1), (14, 99)] 10 == [10, 11, 12]),
         ("certificateJobs: 2 at 21 GiB, 1 at 1 GiB, 4 at 64 GiB",
          certificateJobs (g 21) est == 2 && certificateJobs (g 1) est == 1 &&
          certificateJobs (g 64) est == 4)] do
      IO.println s!"{if ok then "ok  " else "FAIL"} memory limit: {what}"
      unless ok do failed := failed + 1
  return failed

end OpsTest
