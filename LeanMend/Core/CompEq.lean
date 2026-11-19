import LeanMend.Core.DepDiff
import Std.Data.HashMap

/-!
# Computational equality of a changed definition (`docs/static-diff.md` § 4)

A changed `def`, `instance` or `abbrev` gives a Behavior card today, and a
person judges it. This module certifies equality where it holds, with no
target code run (decision S1): the proof-erased body at each side
(`erasedBody`, `probe/Probe.lean`), compared structurally, recursing into
each applied constant — a target constant through the certificate, a
dependency constant through the dependency diff (`LeanMend.Core.DepDiff`,
`docs/static-diff.md` § 1). The shell gathers the data (`LeanMend.Shell.CompEq`:
the probe's new `terms` command, the certificate's open findings, and the
dependency diff), and this module computes the verdict with no IO.

Proof irrelevance means a `theorem`'s or a proof helper's own body is never
compared here, the dependency diff's own rule (`docs/decisions.md` D16,
`LeanMend.Core.DepDiff`'s `DepConst` doc comment): `ConstStatus.targetHeld`
and `ConstStatus.dependencyUnchanged` both stop the recursion with no body
fetched at all, the cost rule "compare by hash first; fetch a full term only
for a hash that differs."
-/

namespace LeanMend

/-- The proof-erased term of a constant's value, structural over `Expr`'s own
constructors (`probe/Probe.lean`, `erasedBody`'s doc comment): the same shape
two probe processes, one per toolchain, give comparably. `ErasedTerm.erased`
is the placeholder for a subterm proof irrelevance erases (`erasedMark`). -/
inductive ErasedTerm where
  | erased
  | bvar (idx : Nat)
  | sort (level : String)
  | const (name : String) (us : List String)
  | app (f a : ErasedTerm)
  | lam (bi : String) (ty body : ErasedTerm)
  | forallE (bi : String) (ty body : ErasedTerm)
  | letE (ty val body : ErasedTerm)
  | nat (v : String)
  | str (v : String)
  | proj (typeName : String) (idx : Nat) (struct : ErasedTerm)
  deriving Repr, DecidableEq, Inhabited

/-- The constants `t` applies, in the order it holds them, one entry per
occurrence (`docs/static-diff.md` § 4 step 4: "for each applied constant,
recurse"). The caller dedups (`List.eraseDups`) before recursing, so a
constant used many times in one body is certified once. -/
partial def ErasedTerm.constants : ErasedTerm → List String
  | .const n _ => [n]
  | .app f a => f.constants ++ a.constants
  | .lam _ ty body => ty.constants ++ body.constants
  | .forallE _ ty body => ty.constants ++ body.constants
  | .letE ty val body => ty.constants ++ val.constants ++ body.constants
  | .proj _ _ s => s.constants
  | .erased | .bvar _ | .sort _ | .nat _ | .str _ => []

/-- A position inside an `ErasedTerm`, innermost last, for naming where two
terms first differ (`docs/static-diff.md` § 4: "the first differing
subterm", decision S3). -/
abbrev Path := List String

/-- The constructor name of `t`, for `firstDiff`'s "different constructor at
this position" case. -/
def ErasedTerm.tag : ErasedTerm → String
  | .erased => "erased" | .bvar _ => "bvar" | .sort _ => "sort" | .const .. => "const"
  | .app .. => "app" | .lam .. => "lam" | .forallE .. => "forallE" | .letE .. => "letE"
  | .nat _ => "nat" | .str _ => "str" | .proj .. => "proj"

/-- Structural equality of two erased terms, at the level of shape only
(`docs/static-diff.md` § 4 step 3): the same binders, and the same
applications of the same constants (by name and universe levels) in the
same order. Two `.const` leaves of the same name are equal here even when
the named constant's own definition differs between toolchains — that
deeper check is `certifyEqual`'s own recursion (step 4), not this one.
Returns the path to the first differing node, outermost first, when the
shapes differ; `none` when they match all the way down. -/
partial def ErasedTerm.firstDiff (a b : ErasedTerm) : Option Path :=
  match a, b with
  | .erased, .erased => none
  | .bvar i, .bvar j => if i == j then none else some [s!"bvar {i}≠{j}"]
  | .sort u, .sort v => if u == v then none else some [s!"sort {u}≠{v}"]
  | .const n us, .const m vs =>
    if n == m && us == vs then none
    else some [if n != m then s!"const {n}≠{m}" else s!"const {n} universes {us}≠{vs}"]
  | .app f1 a1, .app f2 a2 =>
    ((ErasedTerm.firstDiff f1 f2).map ("app.fn" :: ·)) <|>
    ((ErasedTerm.firstDiff a1 a2).map ("app.arg" :: ·))
  | .lam bi1 ty1 bd1, .lam bi2 ty2 bd2 =>
    if bi1 != bi2 then some [s!"lam.binderInfo {bi1}≠{bi2}"] else
    ((ErasedTerm.firstDiff ty1 ty2).map ("lam.ty" :: ·)) <|>
    ((ErasedTerm.firstDiff bd1 bd2).map ("lam.body" :: ·))
  | .forallE bi1 ty1 bd1, .forallE bi2 ty2 bd2 =>
    if bi1 != bi2 then some [s!"forallE.binderInfo {bi1}≠{bi2}"] else
    ((ErasedTerm.firstDiff ty1 ty2).map ("forallE.ty" :: ·)) <|>
    ((ErasedTerm.firstDiff bd1 bd2).map ("forallE.body" :: ·))
  | .letE ty1 v1 bd1, .letE ty2 v2 bd2 =>
    ((ErasedTerm.firstDiff ty1 ty2).map ("letE.ty" :: ·)) <|>
    ((ErasedTerm.firstDiff v1 v2).map ("letE.val" :: ·)) <|>
    ((ErasedTerm.firstDiff bd1 bd2).map ("letE.body" :: ·))
  | .nat v1, .nat v2 => if v1 == v2 then none else some [s!"nat {v1}≠{v2}"]
  | .str v1, .str v2 => if v1 == v2 then none else some [s!"str {v1}≠{v2}"]
  | .proj t1 i1 s1, .proj t2 i2 s2 =>
    if t1 != t2 || i1 != i2 then some [s!"proj {t1}.{i1}≠{t2}.{i2}"]
    else (ErasedTerm.firstDiff s1 s2).map ("proj.struct" :: ·)
  | a, b => some [s!"shape {a.tag}≠{b.tag}"]

/-- One equation lemma of a recursive `def`, erased (`docs/static-diff.md`
§ 4, decision S8): the pattern side (`lhs`, the constant applied to the
matched arguments) and the value side (`rhs`), both erased the same way a
value is (proof subterms replaced by the placeholder). `binders` is the
count of the equation's own universally quantified variables, recorded
for a card; the comparison itself is on `lhs` and `rhs`. -/
structure Equation where
  binders : Nat
  lhs : ErasedTerm
  rhs : ErasedTerm
  deriving Repr, DecidableEq, Inhabited

/-- The applied constants of one equation's `lhs` and `rhs` (the same
recursion source `compareTerms` uses for a matching body, decision S8). -/
def Equation.constants (e : Equation) : List String := e.lhs.constants ++ e.rhs.constants

/-- Whether two constants' equations match, pairwise, in the order the
equation compiler gave them (decision S8): the same count, and each pair's
`lhs` and `rhs` structurally equal (`ErasedTerm.firstDiff`). `none` when
they match; `some path` to the first differing equation and subterm
otherwise. A constant's equations are not themselves sorted or matched by
content, because the equation compiler already gives both sides the
pattern cases in the same source order, for the same source patterns
(decision D5: lean-mend edits no statement, so the match arms' own order
is the target's, unchanged). -/
def compareEquations (before after : List Equation) : Option Path :=
  if before.length != after.length then
    some [s!"equation count {before.length}≠{after.length}"]
  else
    (before.zip after).zipIdx.findSome? fun ((b, a), i) =>
      ((ErasedTerm.firstDiff b.lhs a.lhs).map (s!"eqn {i}.lhs" :: ·)) <|>
      ((ErasedTerm.firstDiff b.rhs a.rhs).map (s!"eqn {i}.rhs" :: ·))

/-- A stated trust point (decision S4): `extern`, `implemented_by` or
`opaque`, compared by name only, never recursed. Every certificate that
relies on one lists it. -/
structure TrustPoint where
  name : String
  kind : String
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The verdict for one declaration's computational equality
(`docs/static-diff.md` § 4): every subterm, all the way down, matches
structurally (`certified`, with the trust points relied on), or the first
differing subterm and its constant (`differsAt`, decision S3). -/
inductive CompEqResult where
  | certified (trustPoints : List TrustPoint)
  | differsAt (constant : String) (reason : String)
  deriving Repr, DecidableEq, Inhabited

/-- Whether `certifyEqual` recurses into a constant's own body, and why not
when it does not (`docs/static-diff.md` § 4 step 4): the shell computes this
from the probe's `terms` output, the certificate's open findings, and the
dependency diff (`LeanMend.Shell.CompEq`). -/
inductive ConstStatus where
  /-- `extern`/`implemented_by`/`opaque` (decision S4): compared by name
  only, listed as a trust point. -/
  | trustPoint (kind : String)
  /-- A dependency constant the dependency diff does not list: its hash
  matched at both sides (`LeanMend.Core.DepDiff.depDiff`), so it is equal
  with no body fetched. -/
  | dependencyUnchanged
  /-- A dependency constant whose axiom set differs, or that exists at
  one side only (`LeanMend.Core.DepDiff.DepDiffKind.axioms`/`onlyBefore`/
  `onlyAfter`): not equal, this constant is the cause. There is no body to
  recurse into for an axiom change or an absent side, unlike a body
  change (below). `reason` names which. -/
  | dependencyTerminal (reason : String)
  /-- A `def`/`instance`/`abbrev` dependency constant whose axiom set
  matches but whose proof-erased body hash differs
  (`LeanMend.Core.DepDiff.DepDiffKind.body`): recurse into its own erased
  body at each side, the same as a target constant with an open finding,
  so the first differing subterm is named precisely (for example a
  changed matcher auxiliary inside the dependency, not only the
  dependency's own name) rather than stopping at "its body differs". -/
  | dependencyBodyDiffers
  /-- A target constant with no open finding at the certificate: already
  held by the certificate's own axiom and statement check. Equal, no body
  fetched. -/
  | targetHeld
  /-- A target constant with an open Behavior finding: recurse into its own
  erased body at each side. -/
  | targetOpen
  /-- A target constant with an open Violation finding: its own axiom set
  differs. Not equal. -/
  | targetAxiomsDiffer
  deriving Repr, DecidableEq, Inhabited


mutual

/-- Certify the computational equality of `root`'s body (a changed `def`,
`instance` or `abbrev`, `docs/static-diff.md` § 4), given each recursed
constant's erased body at each side where one was fetched (`bodyOf`, `none`
for a constant whose body was never needed — a trust point, an unchanged
dependency, or a held target constant), its equations at each side where
fetched (`eqnsOf`, decision S8), and each constant's status (`statusOf`).
Memoizes per constant name (`memo`, threaded through and returned): a
constant reached from more than one place in the term, or from more than
one Behavior finding in the same run, is certified once
(`docs/static-diff.md` § 4, "Memoize per constant pair"). Before recursing
into `name`'s own body, the memo gets a provisional `certified []` entry
for `name` (`guarded`): a recursive `def` applies itself in its own body
(`List.replicate`'s own equations hold `List.replicate` on the right-hand
side, EquiVM's own measured case), so the comparison of `name`'s body, or
of its equations, reaches `name` again before its real verdict is known.
The guard is sound by the standard coinductive argument: assuming `name`
equal, every site the comparison would otherwise still need to check
(the shape of `name`'s own body or equations, which already determines
every self-call's position) is exactly what proves `name` equal, so the
assumption only ever re-confirms itself, never smuggles in an unrelated
fact. The provisional entry is overwritten with the real verdict once
computed, so a reader of the returned `memo` never sees it. -/
partial def certifyEqual (bodyOf : String → Option (ErasedTerm × ErasedTerm))
    (statusOf : String → ConstStatus) (eqnsOf : String → Option (List Equation × List Equation))
    (memo : Std.HashMap String CompEqResult) (name : String) :
    CompEqResult × Std.HashMap String CompEqResult :=
  match memo[name]? with
  | some r => (r, memo)
  | none =>
    match statusOf name with
    | .trustPoint kind => let r := CompEqResult.certified [{ name, kind }]; (r, memo.insert name r)
    | .dependencyUnchanged => let r := CompEqResult.certified []; (r, memo.insert name r)
    | .dependencyTerminal reason =>
      let r := CompEqResult.differsAt name reason; (r, memo.insert name r)
    | .targetHeld => let r := CompEqResult.certified []; (r, memo.insert name r)
    | .targetAxiomsDiffer =>
      let r := CompEqResult.differsAt name
        "its own axiom set differs between the two toolchains"
      (r, memo.insert name r)
    | .targetOpen | .dependencyBodyDiffers =>
      match bodyOf name with
      | none =>
        let r := CompEqResult.differsAt name "no erased body was fetched for it"
        (r, memo.insert name r)
      | some (before, after) =>
        let guarded := memo.insert name (CompEqResult.certified [])
        let (r, memo') := compareTerms bodyOf statusOf eqnsOf guarded name before after
        (r, memo'.insert name r)

/-- `certifyEqual` on every name of `names`, in order, stopping at the
first that differs (decision S3): the shared fold both the matching-body
path and the matching-equations path of `compareTerms` use. -/
partial def recurseInto (bodyOf : String → Option (ErasedTerm × ErasedTerm))
    (statusOf : String → ConstStatus) (eqnsOf : String → Option (List Equation × List Equation))
    (memo : Std.HashMap String CompEqResult) (names : List String) :
    CompEqResult × Std.HashMap String CompEqResult :=
  names.foldl (init := (CompEqResult.certified [], memo)) fun (acc, memo) n =>
    match acc with
    | .differsAt .. => (acc, memo)
    | .certified tps =>
      let (r, memo) := certifyEqual bodyOf statusOf eqnsOf memo n
      match r with
      | .certified tps' => (.certified (tps ++ tps').eraseDups, memo)
      | .differsAt c reason => (.differsAt c reason, memo)

/-- Compare `before` and `after`, the erased bodies of `root` at the two
toolchains (`docs/static-diff.md` § 4 steps 3-4): `ErasedTerm.firstDiff`
for the structural shape; on a match, `recurseInto` every distinct
constant either side applies (decision S3, "the first differing
subterm"). A shape difference (not at a single `.const` leaf — a
different binder, a different literal, a different application order,
a different recursion encoding) falls back to `root`'s equations
(decision S8, `eqnsOf`) when both sides have them: a total,
non-partial `def`'s equation lemmas state every case the equation
compiler proved exhaustive, so they determine the function uniquely by
induction on its own recursion, independently of how that recursion
compiles (structural, well-founded, `brecOn`). `compareEquations` equal
recurses into the equations' own constants the same way a matching body
does; equations unavailable, of different count, or themselves
differing falls back to naming `root` with the body's own differing
subterm — the difference is in `root`'s own compiled form, not in a
named helper. -/
partial def compareTerms (bodyOf : String → Option (ErasedTerm × ErasedTerm))
    (statusOf : String → ConstStatus) (eqnsOf : String → Option (List Equation × List Equation))
    (memo : Std.HashMap String CompEqResult) (root : String)
    (before after : ErasedTerm) : CompEqResult × Std.HashMap String CompEqResult :=
  match ErasedTerm.firstDiff before after with
  | none =>
    recurseInto bodyOf statusOf eqnsOf memo (before.constants ++ after.constants).eraseDups
  | some path =>
    match eqnsOf root with
    | some (beq, aeq) =>
      match compareEquations beq aeq with
      | none =>
        recurseInto bodyOf statusOf eqnsOf memo
          ((beq.flatMap Equation.constants ++ aeq.flatMap Equation.constants).eraseDups)
      | some _ =>
        let desc := "/".intercalate path
        (.differsAt root
          s!"the erased bodies differ at {desc}, and its equations do not match either", memo)
    | none =>
      let desc := "/".intercalate path
      (.differsAt root s!"the erased bodies differ at {desc}", memo)

end

end LeanMend
