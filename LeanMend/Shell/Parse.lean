import Lean.Data.Json
import LeanMend.Spec.Types
import LeanMend.Core.Sched

/-!
# Parse at the edge

Raw JSON becomes typed operands here, once (concept B2, stratum 3). Nothing
in `Core` sees `Json`. Each parser returns `Except String`, and the message
names the field that failed. See `docs/architecture.md` § The version boundary
for the probe's JSON, and `tests/fixtures/diagnostics/` for `lean --json`.
-/

namespace LeanMend.Parse

open Lean (Json)

private def field {α} [Lean.FromJson α] (j : Json) (k : String) : Except String α :=
  match j.getObjValAs? α k with
  | .ok v => .ok v
  | .error e => .error s!"field '{k}': {e}"

def severity : String → Except String Severity
  | "error" => .ok .error
  | "warning" => .ok .warning
  | "information" => .ok .information
  | s => .error s!"unknown severity '{s}'"

/-- One line of `lean --json` output. `module` is not in the JSON; the shell
knows which module it compiled. -/
def diagnostic (module : String) (j : Json) : Except String Diagnostic := do
  let pos ← field (α := Json) j "pos"
  -- `endPos` is null for some messages (a deprecated-module warning): the
  -- range is then the start position.
  let endPos ← match j.getObjValD "endPos" with
    | Json.null => pure pos
    | e => pure e
  pure {
    module
    line := ← field pos "line"
    column := ← field pos "column"
    endLine := ← field endPos "line"
    endColumn := ← field endPos "column"
    severity := ← severity (← field j "severity")
    kind := ← field j "kind"
    text := ← field j "data" }

def declKind : String → Except String DeclKind
  | "theorem" => .ok .theorem
  | "def" => .ok .def
  | "instance" => .ok .instance
  | "abbrev" => .ok .abbrev
  | "axiom" => .ok .axiom
  | "inductive" => .ok .inductive
  | "structure" => .ok .structure
  | "class" => .ok .class
  | "other" => .ok .other
  | s => .error s!"unknown declaration kind '{s}'"

/-- The hash lean-mend stores for a region's text: `String.hash`, as hex. The
shell computes it under lean-mend's own toolchain, so one function hashes the
baseline and the after certificate. -/
def textHash (s : String) : String :=
  String.ofList (Nat.toDigits 16 s.hash.toNat)

/-- The axiom set of a declaration, as `compare` sees it: sorted, without
duplicates, and with every generated `native_decide` axiom
(`X._native.native_decide.ax_1_12`) collapsed to the one name
`native_decide`. Lean numbers those axioms per declaration, so their names can
change between toolchains when the trust does not. -/
def axiomSet (raw : List String) : List String :=
  let norm := raw.map fun a =>
    if (a.splitOn "._native.native_decide.ax_").length > 1 then "native_decide" else a
  (norm.eraseDups.toArray.qsort (· < ·)).toList

/-- One line of the probe's `decls` output. `norm` rewrites region text
before it is hashed (`AliasMap.normalize`), so the same alias map applies to
the baseline and the after certificate. The statement hash is of the
statement's token sequence (`statementTokens`, one space between tokens), not
of its text, so whitespace and comments do not count
(`docs/verification.md` § The certificate). A space is not an identifier
character, so `norm` sees each token as it would alone. -/
def decl (norm : String → String) (j : Json) : Except String Decl := do
  let tokens : List String ← field j "statementTokens"
  pure {
    name := ← field j "name"
    module := ← field j "module"
    kind := ← declKind (← field j "kind")
    statementHash := textHash (norm (" ".intercalate tokens))
    bodyHash := textHash (norm (← field j "body"))
    axioms := axiomSet (← field j "axioms") }

/-- One line of the probe's `decls` output: a row (`decl`), or an `unread`
line, which names a declaration that the certificate selects but whose row
the probe cannot give (`docs/verification.md` § The certificate). -/
def declLine (norm : String → String) (j : Json) : Except String (Except DeclUnread Decl) :=
  match j.getObjVal? "unread" with
  | .ok _ => do
    pure (.error { module := ← field j "module", decl := ← field j "name",
                   reason := ← field j "unread" })
  | .error _ => .ok <$> decl norm j

/-- One line of the probe's `deprecated` output: old name and new name. A
deprecation with no new name gives no alias. -/
def alias_ (j : Json) : Except String (Option (String × String)) := do
  let n : String ← field j "name"
  let new? : Option String ← field j "newName"
  pure (new?.map (n, ·))

/-- Parse every non-empty line of `out` with `p`. The error names the line. -/
def lines {α} (p : Json → Except String α) (out : String) : Except String (List α) :=
  (out.splitOn "\n" |>.filter (· ≠ "")).zipIdx.mapM fun (l, i) =>
    match Json.parse l >>= p with
    | .ok v => .ok v
    | .error e => .error s!"line {i + 1}: {e}"

private def pair (j : Json) (k : String) : Except String (Nat × Nat) := do
  match ← field (α := List Nat) j k with
  | [a, b] => pure (a, b)
  | _ => throw s!"field '{k}' is not a byte range"

/-- One line of the probe's `node` output: the nodes that contain one offset,
innermost first. `src` is the file's text, for each node's own text. -/
def nodes (src : String) (j : Json) : Except String (Nat × List Node) := do
  let offset : Nat ← field j "offset"
  let ns : List Json ← field j "nodes"
  let bytes := src.toUTF8
  let ns ← ns.mapM fun n => do
    let (a, b) ← pair n "range"
    let toks : List Json := (n.getObjValAs? (List Json) "tokens").toOption.getD []
    let toks ← toks.mapM fun t => do
      let (ta, tb) ← pair t "range"
      pure ({ text := ← field t "text", start := ta, stop := tb } : Token)
    let lineStart := (String.fromUTF8! (bytes.extract 0 a)).splitOn "\n" |>.getLast!
    pure { kind := ← field n "kind", start := a, stop := b,
           text := String.fromUTF8! (bytes.extract a b), column := lineStart.length,
           tokens := toks }
  pure (offset, ns)

def errorClass : String → Except String ErrorClass
  | "unknownIdentifier" => .ok .unknownIdentifier
  | "unknownNamespace" => .ok .unknownNamespace
  | "missingDecidable" => .ok .missingDecidable
  | "typeMismatch" => .ok .typeMismatch
  | "simpNoProgress" => .ok .simpNoProgress
  | "unsolvedGoals" => .ok .unsolvedGoals
  | "tacticFailed" => .ok .tacticFailed
  | "binderOverride" => .ok .binderOverride
  | "noGoals" => .ok .noGoals
  | "heartbeat" => .ok .heartbeat
  | "wallclock" => .ok .wallclock
  | "unknown" => .ok .unknown
  | s => .error s!"unknown error class '{s}'"

def family : String → Except String TacticFamily
  | "simp" => .ok .simp | "rw" => .ok .rw | "exact" => .ok .exact
  | "decide" => .ok .decide | "any" => .ok .any
  | s => .error s!"unknown tactic family '{s}'"

def editOp (j : Json) : Except String EditOp := do
  match ← field (α := String) j "op" with
  | "rename" => pure (.rename (← field j "old") (← field j "new"))
  | "renamePrefix" => pure (.renamePrefix (← field j "old") (← field j "new"))
  | "replaceInBody" => pure (.replaceInBody (← field j "decl") (← field j "old") (← field j "new"))
  | "simpArgAdd" => pure (.simpArgAdd (← field j "lemma"))
  | "simpArgAddPrior" => pure (.simpArgAddPrior (← field j "lemma"))
  | "simpaToExact" => pure .simpaToExact
  | "simpaSplit" => pure .simpaSplit
  | "simpaUsingBang" => pure .simpaUsingBang
  | "simpaUsingBangNested" => pure .simpaUsingBangNested
  | "keywordSwap" => pure (.keywordSwap (← field j "from") (← field j "to"))
  | "deleteTactic" => pure .deleteTactic
  | "deleteShowRewrite" => pure .deleteShowRewrite
  | "matchToIf" => pure .matchToIf
  | "matchOnVal" => pure .matchOnVal
  | "valCompare" => pure .valCompare
  | "appendTactic" => pure (.appendTactic (← field j "tactic"))
  | "closeBullet" => pure (.closeBullet (← field j "tactic"))
  | "heartbeats" => pure (.heartbeats (← field j "n"))
  | o => throw s!"unknown op '{o}'"

/-- A rule file (`docs/rules.md` § The rule format), with the loader's
vacuity refusals (concept C9). -/
def rule (j : Json) : Except String Rule := do
  let name : String ← field j "name"
  let cls ← errorClass (← field j "class")
  let entrenchment ← match ← field (α := String) j "entrenchment" with
    | "ratified" => pure Entrenchment.ratified
    | "proposed" => pure .proposed
    | e => throw s!"rule {name}: entrenchment '{e}' (derived rules are never files)"
  let fam ← family (← field j "node")
  let ops ← (← field (α := List Json) j "candidates").mapM editOp
  if ops.isEmpty then throw s!"rule {name}: no candidates (vacuous)"
  if fam == .any && cls == .unknown then throw s!"rule {name}: node any on class unknown (vacuous)"
  if ops.contains .deleteTactic && cls != .simpNoProgress && cls != .noGoals then
    throw s!"rule {name}: deleteTactic is allowed only for simpNoProgress and noGoals"
  -- A rewrite that finds nothing has class tacticFailed ("Tactic `rewrite` failed").
  if ops.contains .deleteShowRewrite && cls != .tacticFailed then
    throw s!"rule {name}: deleteShowRewrite is allowed only for tacticFailed"
  pure { name, cls, entrenchment, family := fam, ops }

/-- The words of one line of a `/proc` file, split at spaces and tabs. -/
private def procWords (l : String) : List String :=
  ((l.replace "\t" " ").splitOn " ").filter (· ≠ "")

/-- The value of the `name:   <n> kB` line of a `/proc` file, in KiB, or
`none` when the file has no such line. -/
def kbField (text name : String) : Except String (Option KiB) := do
  let some line := (text.splitOn "\n").find? (fun l => (procWords l).head? == some s!"{name}:")
    | pure none
  match procWords line with
  | [_, n, "kB"] =>
    match n.toNat? with
    | some v => pure (some ⟨v⟩)
    | none => throw s!"{name}: '{n}' is not a number"
  | _ => throw s!"{name}: the line '{line}' is not '<n> kB'"

/-- `MemAvailable` from the text of `/proc/meminfo`, the input of the default
memory limit (`docs/parallel.md` P24). -/
def memAvailable (meminfo : String) : Except String KiB := do
  let some v ← kbField meminfo "MemAvailable" | throw "/proc/meminfo has no MemAvailable line"
  pure v

/-- The private resident memory of one process, from the text of
`/proc/<pid>/status`: `RssAnon` plus `RssShmem` (`docs/parallel.md` P24).
File pages (`RssFile`, the mapped `.olean` files) are shared between the
processes and the kernel can drop them, so they do not count. A kernel thread
or a zombie has neither line, and holds 0. -/
def privateRss (status : String) : Except String KiB := do
  let anon := ((← kbField status "RssAnon").map (·.val)).getD 0
  let shmem := ((← kbField status "RssShmem").map (·.val)).getD 0
  pure ⟨anon + shmem⟩

/-- The parent pid from the text of `/proc/<pid>/stat`, its fourth field. The
second field, the command name in parentheses, can hold spaces and `)`, so
the fields are read after the last `)`. -/
def statParent (stat : String) : Except String Nat := do
  match procWords ((stat.splitOn ")").getLast!) with
  | _ :: ppid :: _ =>
    match ppid.toNat? with
    | some n => pure n
    | none => throw s!"/proc stat: parent '{ppid}' is not a number"
  | _ => throw s!"/proc stat: no parent field in '{stat}'"

end LeanMend.Parse
