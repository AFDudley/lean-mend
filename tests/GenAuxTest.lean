import LeanMend.Core.GenAux

/-!
# Generated auxiliaries of the target (`LeanMend.Core.GenAux`, `docs/static-diff.md` § 3)

Pure checks over hand-built rows: `auxOwnerRole`'s role classification, and
`genAuxDiff`'s matching by owner and role, not by name, restricted to what a
root declaration's own compiled value actually reaches (`reachableAux`) — the
EquiVM E3 shape (`docs/static-diff.md` § 3, `allocationSizes.match_1`/
`allocationSizes._f`, measured on EquiVM's pins 2026-11-11, `probe explain`
on `mend-cache/probe-base` and `mend-target`): at the before side, the root
declaration's own `uses` never reaches its same-named-pattern matcher (an
equation-lemma artifact, unreached, still carrying a stale axiom); at the
after side, it does, through a `_f` well-founded helper, with a new axiom.
-/

open LeanMend

namespace GenAuxTest

def check (failed : IO.Ref Nat) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}{if ok then "" else s!": {detail}"}"
  unless ok do failed.modify (· + 1)

def dc (name module kind : String) (axioms : List String) (bodyHash : Option String)
    (uses : List String := []) : DepConst :=
  { name, module, kind, axioms, bodyHash, uses }

def run : IO Nat := do
  let failed ← IO.mkRef 0
  -- `auxOwnerRole`: a matcher, a `_f` well-founded helper, a sparse
  -- `casesOn`, a `_proof_N` helper (role `other`, since `_proof_N`'s own
  -- component is neither `match_` nor `_f`), a `deriving` handler's own
  -- output, and a name that is nobody's auxiliary.
  check failed "a matcher's owner and role"
    (auxOwnerRole "allocationSizes.match_1" == some ("allocationSizes", .matcher))
  check failed "a `_f` well-founded helper's owner and role"
    (auxOwnerRole "allocationSizes._f" == some ("allocationSizes", .wfHelperF))
  check failed "a sparse casesOn auxiliary's owner and role"
    (auxOwnerRole "classify._sparseCasesOn_1" == some ("classify", .sparseCasesOn))
  check failed "a `_proof_N` proof helper's owner, role `other`"
    (auxOwnerRole "List.find?_congr._proof_1_1" == some ("List.find?_congr", .other))
  check failed "a `deriving` handler's own output, owner and role"
    (auxOwnerRole "instInhabitedPools.default" == some ("instInhabitedPools", .derivingOutput))
  check failed "a declaration's own name is nobody's auxiliary"
    (auxOwnerRole "allocationSizes" == none)
  check failed "an equation lemma's owner and role (underscore-prefixed shape)"
    (auxOwnerRole "sizes._eq_1" == some ("sizes", .eqnLemma))
  check failed "Lean's real equation-lemma shape, no underscore prefix (Lean.Meta.Eqns)"
    (auxOwnerRole "allocationSizes.eq_1" == some ("allocationSizes", .eqnLemma))
  check failed "the eq_def shape"
    (auxOwnerRole "allocationSizes.eq_def" == some ("allocationSizes", .eqnLemma))
  check failed "a real namespaced name that merely starts with eq_ is not an equation lemma"
    (auxOwnerRole "allocationSizes.eq_uals" == none)
  -- A private-prefixed generated name: the owner stays the public name,
  -- and the role reads the right component past the private prefix
  -- (`docs/verification.md` § The certificate, the EquiVM run 10 case
  -- `_private.Mathlib.Data.List.Find.0.List.find?_congr._proof_1_1`).
  check failed "a private-prefixed proof helper's owner is still the public name"
    (auxOwnerRole "_private.Mathlib.Data.List.Find.0.List.find?_congr._proof_1_1" ==
      some ("List.find?_congr", .other))

  -- `genAuxDiff`, the EquiVM E3 shape exactly: at the before side,
  -- `allocationSizes`'s own `uses` never reaches `match_7`, which exists in
  -- the module (an unreached equation-lemma artifact, already carrying
  -- `propext`) but is not on `allocationSizes`'s own path, so it is not
  -- grouped under `allocationSizes` at all. At the after side,
  -- `allocationSizes` uses `allocationSizes._f`, which uses
  -- `allocationSizes.match_1` (`propext`) — reachable, so it is grouped.
  -- Matched by owner and role (both `allocationSizes`/`matcher`), not by
  -- name (`match_7` against `match_1`): the before side has nothing
  -- reachable under that key, the after side gains one with `propext` —
  -- an `onlyAfter` entry, predicting a Violation.
  let before : List DepConst :=
    [dc "allocationSizes" "Stele.Interp" "def" [] (some "#r") ["Stele.Expr", "List"],
     dc "allocationSizes.match_7" "Stele.Interp" "def" ["propext"] (some "#1")]
  let after : List DepConst :=
    [dc "allocationSizes" "Stele.Interp" "def" ["propext"] (some "#r") ["Stele.Expr", "List",
       "allocationSizes._f"],
     dc "allocationSizes._f" "Stele.Interp" "def" ["propext"] (some "#f") ["allocationSizes.match_1"],
     dc "allocationSizes.match_1" "Stele.Interp" "def" ["propext"] (some "#2")]
  let es := genAuxDiff before after
  check failed "two entries: allocationSizes's matcher and its _f helper, reachable only at the after side"
    (es.length == 2) (repr es |>.pretty)
  let matcherEntry := es.find? (·.role == .matcher)
  check failed "the matcher entry's owner is allocationSizes"
    (matcherEntry.map (·.owner) == some "allocationSizes")
  check failed "every entry is onlyAfter: nothing reachable under either key at the before side"
    (es.all (·.kind == .onlyAfter)) (repr (es.map (·.kind)) |>.pretty)
  check failed "the matcher entry's after auxiliary is match_1, not the unreached match_7"
    ((matcherEntry.bind (·.after)).map (·.const.name) == some "allocationSizes.match_1")
  check failed "the wfHelperF role (allocationSizes._f) is also reachable only at the after side"
    (es.any fun e => e.owner == "allocationSizes" && e.role == .wfHelperF && e.kind == .onlyAfter)

  -- The prediction: a target declaration whose auxiliary gains an axiom
  -- becomes a predicted Violation — here by appearing at the after side
  -- only, with a nonempty axiom set, the `onlyAfter` shape
  -- (`docs/static-diff.md` § 3, the real E3 shape; `.axioms`-with-gain is
  -- the other shape, checked below).
  let ps := predictionsOf es
  check failed "the matcher's onlyAfter appearance, carrying propext, predicts one Violation"
    (ps.any fun p => p.owner == "allocationSizes" && p.role == .matcher &&
      p.added == ["propext"] && p.cause == "allocationSizes.match_1") (repr ps |>.pretty)

  -- The ordinary axiom-gain shape: a matcher reachable at both sides,
  -- under the same name, whose axiom set grows.
  let gainBefore : List DepConst :=
    [dc "f" "App" "def" [] (some "#r") ["f.match_1"], dc "f.match_1" "App" "def" [] (some "#1")]
  let gainAfter : List DepConst :=
    [dc "f" "App" "def" ["propext"] (some "#r") ["f.match_1"],
     dc "f.match_1" "App" "def" ["propext"] (some "#1")]
  let gainEs := genAuxDiff gainBefore gainAfter
  check failed "an axiom gain on a reachable matcher of the same name is an axioms entry"
    (gainEs.map (·.kind) == [.axioms ["propext"] []]) (repr (gainEs.map (·.kind)) |>.pretty)
  check failed "the axiom gain predicts one Violation, cause the after-side auxiliary"
    (predictionsOf gainEs == [{ owner := "f", role := .matcher, added := ["propext"],
                                 cause := "f.match_1" }]) (repr (predictionsOf gainEs) |>.pretty)

  -- Regression: an equation lemma (`h.eq_1`, no underscore prefix) is
  -- itself a generated auxiliary, not an independent root. Before this
  -- was recognized, `h.eq_1` was classified a real declaration and so
  -- its own `reachableAux` walk (its proof term cites the matcher it
  -- unfolds) made `h`'s matcher falsely reachable at a side where `h`
  -- itself never reaches it — measured on EquiVM's pins, where
  -- `allocationSizes.eq_N` made the before side falsely reach
  -- `allocationSizes.match_1`, masking the real E3 finding (the matcher
  -- is unreachable from `h` directly, reachable only through `eq_1`).
  let eqnBefore : List DepConst :=
    [dc "h" "App" "def" [] (some "#r") [], dc "h.eq_1" "App" "theorem" [] (some "#p") ["h.match_1"],
     dc "h.match_1" "App" "def" [] (some "#1")]
  let eqnAfter : List DepConst :=
    [dc "h" "App" "def" ["propext"] (some "#r") ["h._f"],
     dc "h._f" "App" "def" ["propext"] (some "#f") ["h.match_1"],
     dc "h.match_1" "App" "def" ["propext"] (some "#1")]
  let eqnEs := genAuxDiff eqnBefore eqnAfter
  let eqnMatcher := eqnEs.find? (·.role == .matcher)
  check failed "the matcher is onlyAfter, not reached at the before side through the equation lemma"
    (eqnMatcher.map (·.kind) == some .onlyAfter) (repr eqnEs |>.pretty)

  -- Regression: a `where`-bound helper's own inner match, named flatly
  -- under the PARENT's numbering at one toolchain (`allocationSizes.
  -- match_1`, not `allocationSizes.refExprs.match_1`) — Lean's own
  -- naming quirk, measured on EquiVM's pins at v4.29.0. The helper
  -- (`refExprs`) is its own root and the one whose `uses` actually
  -- reaches the match; grouping by the match's own name-parsed owner
  -- (`allocationSizes`, since the name has only one nesting level) would
  -- attribute it to the wrong declaration regardless of which root's
  -- walk found it. Grouping by the discovering root fixes this: the
  -- match's role (`matcher`) still comes from its own name, but its
  -- owner is `refExprs`, not `allocationSizes`.
  let flatBefore : List DepConst :=
    [dc "allocationSizes" "Stele.Interp" "def" [] (some "#r") [],
     dc "allocationSizes.refExprs" "Stele.Interp" "def" [] (some "#w") ["allocationSizes.match_1"],
     dc "allocationSizes.match_1" "Stele.Interp" "def" [] (some "#1")]
  let flatAfter : List DepConst :=
    [dc "allocationSizes" "Stele.Interp" "def" [] (some "#r") [],
     dc "allocationSizes.refExprs" "Stele.Interp" "def" [] (some "#w") ["allocationSizes.refExprs.match_1"],
     dc "allocationSizes.refExprs.match_1" "Stele.Interp" "def" [] (some "#2")]
  let flatEs := genAuxDiff flatBefore flatAfter
  check failed "the match is attributed to refExprs (the discovering root), not allocationSizes"
    (flatEs.all fun e => e.owner == "allocationSizes.refExprs") (repr flatEs |>.pretty)
  check failed "no entry for allocationSizes itself: the flat-naming quirk does not leak into its group"
    (flatEs.all (·.owner != "allocationSizes")) (repr flatEs |>.pretty)

  -- An auxiliary reachable at the before side only: reported, with its
  -- role, and predicts no Violation (the before side carries no axiom to
  -- gain from; `predictionsOf` only predicts an `onlyAfter` with a
  -- nonempty axiom set).
  let onlyBefore : List DepConst :=
    [dc "g" "App" "def" [] (some "#r") ["g._f"], dc "g._f" "App" "def" [] (some "#1")]
  let onlyAfterRows : List DepConst := [dc "g" "App" "def" [] (some "#r")]
  let gone := genAuxDiff onlyBefore onlyAfterRows
  check failed "an auxiliary reachable at the before side only is onlyBefore, with its role"
    (gone == [{ owner := "g", role := .wfHelperF, kind := .onlyBefore,
                before := some { owner := "g", role := .wfHelperF,
                                  const := (dc "g._f" "App" "def" [] (some "#1")) },
                after := none }]) (repr gone |>.pretty)
  check failed "an onlyBefore entry predicts no Violation"
    (predictionsOf gone == [])

  -- A `theorem`-kind auxiliary (a `_proof_N` helper): proof irrelevance
  -- means a body-hash difference alone gives no entry, only its axiom set
  -- matters (`docs/static-diff.md` Finding 4 of the design review).
  let thmBefore : List DepConst :=
    [dc "h" "App" "theorem" [] (some "#r") ["h._proof_1_1"], dc "h._proof_1_1" "App" "theorem" [] (some "#a")]
  let thmAfter : List DepConst :=
    [dc "h" "App" "theorem" [] (some "#r") ["h._proof_2_1"], dc "h._proof_2_1" "App" "theorem" [] (some "#b")]
  check failed "a theorem-kind auxiliary's body-hash difference is no entry"
    (genAuxDiff thmBefore thmAfter == [])

  -- A `def`-kind auxiliary with the same axiom set but a different body
  -- hash: a body-changed entry.
  let defBefore : List DepConst :=
    [dc "k" "App" "def" [] (some "#r") ["k.match_1"], dc "k.match_1" "App" "def" [] (some "#a")]
  let defAfter : List DepConst :=
    [dc "k" "App" "def" [] (some "#r") ["k.match_1"], dc "k.match_1" "App" "def" [] (some "#b")]
  check failed "a def-kind auxiliary's body-hash difference, same axioms, is a body-changed entry"
    ((genAuxDiff defBefore defAfter).map (·.kind) == [.body])

  -- Identical rows: no entry.
  check failed "identical rows give no entry" (genAuxDiff gainBefore gainBefore == [])

  -- Another declaration's auxiliary is not `root`'s. The EquiVM shape: a
  -- theorem's proof reaches `Theory.initState.eq_1`, an equation lemma of a
  -- different declaration, which gains axioms. That gives `initState` an
  -- entry, never the theorem that only uses it.
  let foreignBefore : List DepConst :=
    [dc "App.uses_init" "App" "theorem" [] none ["Theory.initState.eq_1"],
     dc "Theory.initState" "App" "def" [] (some "#i") [],
     dc "Theory.initState.eq_1" "App" "theorem" [] none []]
  let foreignAfter : List DepConst :=
    [dc "App.uses_init" "App" "theorem" ["Classical.choice"] none ["Theory.initState.eq_1"],
     dc "Theory.initState" "App" "def" [] (some "#i") [],
     dc "Theory.initState.eq_1" "App" "theorem" ["Classical.choice"] none []]
  let foreign := genAuxDiff foreignBefore foreignAfter
  check failed "another declaration's equation lemma is never the user's auxiliary"
    (foreign.all (·.owner != "App.uses_init")) (repr foreign |>.pretty)
  return ← failed.get

end GenAuxTest
