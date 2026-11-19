import LeanMend
import CauseTest

/-!
# Level 3: `FindingMending` (`LeanMend.Core.Mend`, `LeanMend.Core.Cause`)

`classifyCause` and the axiom-finding rule match (`docs/rules.md` §
Axiom-finding rules), then `FindingMending.step` and `FindingMending.next`
on a hand-built repair-frontier module with two sites and three findings
(`docs/machine.md` § Level 3, § FindingMending).
-/

open LeanMend
open CauseTest (check owned dep core mkCause)

namespace FindingMendingTest

/-- `t` is a `body` edit of `decl` (`Candidate`/`EditTarget` derive no
`BEq`, so a comparison matches on the constructor instead). -/
def isBodyAt (t : EditTarget) (decl : String) : Bool :=
  match t with | .body d => d == decl | _ => false

/-- `t` is a `beforeDecl` insertion at `decl`. -/
def isBeforeDeclAt (t : EditTarget) (decl : String) : Bool :=
  match t with | .beforeDecl d => d == decl | _ => false

/-- `a` is `attempt` at the site keyed `site`, with the rule named `rule`
(`FindingAction` derives no `BEq` either, since it carries a `Candidate`). -/
def isAttempt (a : FindingAction) (site : SiteKey) (rule : String) : Bool :=
  match a with | .attempt g c => g.key == site && c.rule == rule | _ => false

def isGiveUp (a : FindingAction) (site : SiteKey) : Bool :=
  match a with | .giveUp g => g.key == site | _ => false

def isFinish (a : FindingAction) : Bool :=
  match a with | .finish => true | _ => false

/-- A `Node` that holds one `simp` tactic, the shape `causeTactic` reports
for the `simp-congr-classical` rule shape (`docs/rules.md`). -/
def simpNode : Node :=
  { kind := "Lean.Parser.Tactic.simp", start := 100, stop := 113, column := 2,
    text := "simp only [a]",
    tokens := [{ text := "simp", start := 100, stop := 104 }] }

def congrRule : Rule :=
  { name := "simp-congr-classical", cls := .axiomsAdded, entrenchment := .proposed,
    family := .simp, causeTag := some .congrLemma, ops := [.keywordSwap "simp" "dsimp"] }

def matcherRule : Rule :=
  { name := "match-sparse-cases", cls := .axiomsAdded, entrenchment := .proposed,
    family := .any, causeTag := some .matcher,
    ops := [.setOptionBefore "backward.match.sparseCases" "false"] }

/-- An added-axiom cause through a dependency's `congr` lemma, the shape
`simp-congr-classical` targets. -/
def congrCause : AxiomCause :=
  mkCause [owned "App.foo" "App", dep "Lib.congr" "Mathlib.X"] (dep "Lib.congr" "Mathlib.X")

/-- An added-axiom cause whose own module is removed, for the class
mismatch check. -/
def removedCause : AxiomCause :=
  mkCause [owned "App.foo" "App", dep "Lib.congr" "Mathlib.X"] (dep "Lib.congr" "Mathlib.X")
    (change := .removed)

def checkRuleMatch (failed : IO.Ref Nat) : IO Unit := do
  check failed "classifyCause: an added axiom is axiomsAdded"
    (classifyCause congrCause == .axiomsAdded)
  check failed "classifyCause: a removed axiom is axiomsRemoved"
    (classifyCause removedCause == .axiomsRemoved)
  check failed "causeTagMatches: none matches every tag (a rule with no causeTag)"
    (causeTagMatches none .congrLemma && causeTagMatches none .matcher)
  check failed "causeTagMatches: some .any matches every tag"
    (causeTagMatches (some .any) .congrLemma && causeTagMatches (some .any) .matcher)
  check failed "causeTagMatches: some t matches only t"
    (causeTagMatches (some .congrLemma) .congrLemma &&
     !causeTagMatches (some .congrLemma) .matcher)
  -- `simp-congr-classical`: class and causeTag match, the node holds `simp`.
  let got := findingRuleCandidates congrRule .congrLemma congrCause "App.foo" 90 (some simpNode) none
  check failed "simp-congr-classical: keywordSwap turns simp into dsimp, in the tactic node"
    (got.map (·.replacement) == ["dsimp only [a]"] &&
     (got.map (·.target)).all (isBodyAt · "App.foo"))
    (toString (got.map (·.replacement)))
  -- causeTag mismatch: the rule wants a congr lemma, the site is a matcher.
  check failed "causeTag mismatch gives no candidate"
    (findingRuleCandidates congrRule .matcher congrCause "App.foo" 90 (some simpNode) none).isEmpty
  -- class mismatch: the rule is for axiomsAdded, the cause is a removed axiom.
  check failed "class mismatch gives no candidate"
    (findingRuleCandidates congrRule .congrLemma removedCause "App.foo" 90 (some simpNode) none).isEmpty
  -- no node: an operation that edits a tactic node gets no candidate.
  check failed "no tactic node, no candidate, for an operation that needs one"
    (findingRuleCandidates congrRule .congrLemma congrCause "App.foo" 90 none none).isEmpty
  -- `match-sparse-cases`: setOptionBefore needs only the declaration start.
  let got2 := findingRuleCandidates matcherRule .matcher congrCause "App.foo" 90 none none
  check failed "match-sparse-cases: setOptionBefore inserts before the declaration, no node needed"
    (got2.map (·.replacement) == ["set_option backward.match.sparseCases false in\n"] &&
     (got2.map (·.target)).all (isBeforeDeclAt · "App.foo") &&
     got2.map (·.start) == [90] && got2.map (·.stop) == [90])
    (repr got2 |>.pretty)

/-- Two findings closed at one site, `App.foo` (`App.foo`'s cause is
`Lib.congr`). -/
def groupA : FindingSiteGroup :=
  { key := { site := ("App.foo", "App"), cause := .const "Lib.congr" "Mathlib.X" .added },
    first := congrCause,
    members := [("c-1", "App.foo", ["Classical.choice"]), ("c-2", "App.foo", ["Classical.choice"])] }

/-- One finding at a second site, `App.bar`. -/
def groupB : FindingSiteGroup :=
  { key := { site := ("App.bar", "App"), cause := .const "Lib.other" "Mathlib.X" .added },
    first := mkCause [owned "App.bar" "App", dep "Lib.other" "Mathlib.X"]
      (dep "Lib.other" "Mathlib.X"),
    members := [("c-3", "App.bar", ["Classical.choice"])] }

def mkCandidate (name : String) : Candidate :=
  { rule := name, entrenchment := .proposed, target := .body "D", start := 0, stop := 1,
    replacement := name, tokens := [] }

def cA : Candidate := mkCandidate "accept-at-foo"
def cB1 : Candidate := mkCandidate "reject-at-bar-1"
def cB2 : Candidate := mkCandidate "reject-at-bar-2"

/-- A repair-frontier module with two open sites: `App.foo` (two findings,
one candidate, to be accepted) and `App.bar` (one finding, two candidates,
both to be rejected until the site is exhausted). -/
def m0 : FindingMending :=
  { module := "App", sites := [⟨groupA, [cA]⟩, ⟨groupB, [cB1, cB2]⟩], exhausted := [],
    accepted := [], nonempty := by decide }

def checkStepMachine (failed : IO.Ref Nat) : IO Unit := do
  check failed "the head site is App.foo, with its one candidate"
    (isAttempt m0.next groupA.key cA.rule)
  -- Accept at App.foo, reject both candidates at App.bar, then give up:
  -- chained in the `Except` monad, each step feeding the next.
  let chain : Except Refusal (FindingMending × FindingMending × FindingMending × FindingMending) :=
    do
      let m1 ← m0.step (.accepted true true true)
      let m2 ← m1.step .rejected
      let m3 ← m2.step .rejected
      let m4 ← m3.step .gaveUp
      pure (m1, m2, m3, m4)
  match chain with
  | .error _ => check failed "the chain accept / reject / reject / giveUp succeeds" false
  | .ok (m1, m2, m3, m4) =>
    check failed "accepting closes both of App.foo's findings"
      (m1.accepted.map (·.closed) == [groupA.members]) (toString (m1.accepted.map (·.closed)))
    check failed "accepting commits the candidate and records the site"
      (m1.accepted.map (·.candidate.rule) == [cA.rule] && m1.accepted.map (·.site) == [groupA.key])
    check failed "App.bar is now the only open site, head candidate reject-at-bar-1"
      (m1.sites.map (·.group.key) == [groupB.key] && isAttempt m1.next groupB.key cB1.rule)
    check failed "accepting lowers openFindingCount by App.foo's two findings"
      (m0.openFindingCount == 3 && m1.openFindingCount == 1) (toString m1.openFindingCount)
    check failed "rejecting the first App.bar candidate leaves the second, the site stays open"
      (m2.sites.map (·.candidates.map (·.rule)) == [[cB2.rule]] &&
       isAttempt m2.next groupB.key cB2.rule)
    check failed "rejecting closes no finding; App.bar's finding still counts as open"
      (m2.openFindingCount == m1.openFindingCount && m2.accepted.length == m1.accepted.length)
    check failed "rejecting lowers candidatesLeft by one"
      (m2.candidatesLeft + 1 == m1.candidatesLeft) (toString m2.candidatesLeft)
    check failed "rejecting App.bar's last candidate empties its list, so next is giveUp"
      (isGiveUp m3.next groupB.key && m3.openFindingCount == m2.openFindingCount)
    check failed "giving up moves App.bar's declaration to exhausted, and no site is left"
      (m4.exhausted == ["App.bar"] && m4.sites.isEmpty && isFinish m4.next)
    check failed "every open finding is now resolved or exhausted: openFindingCount is 0"
      (m4.openFindingCount == 0) (toString m4.openFindingCount)
    -- The accepted patch's own fields: closed is non-empty, `noNewFinding`
    -- is true, matching `FindingAccepted.closes_at_least_one` and
    -- `.adds_no_finding`.
    match m1.accepted with
    | [a] =>
      check failed "the accepted patch closes at least one finding and adds none"
        (!a.closed.isEmpty && a.noNewFinding == true)
    | _ => check failed "exactly one accepted patch" false
    -- A reject with no candidate attempted (App.bar's list is already
    -- empty at `m3`) is refused, not silently accepted.
    match m3.step .rejected with
    | .error _ => check failed "rejected with no candidate attempted is refused" true
    | .ok _ => check failed "rejected with no candidate attempted is refused" false
  -- A giveUp while the head site still has a candidate is refused.
  match m0.step .gaveUp with
  | .error _ => check failed "gaveUp with candidates left is refused" true
  | .ok _ => check failed "gaveUp with candidates left is refused" false

def run : IO Nat := do
  let failed ← IO.mkRef 0
  checkRuleMatch failed
  checkStepMachine failed
  return ← failed.get

end FindingMendingTest
