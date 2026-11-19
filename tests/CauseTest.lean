import LeanMend.Core.Cause

/-!
# The cause of a finding (`LeanMend.Core.Cause`)

Small dependency graphs, written by hand, with the expected path, cause and
groups worked out by hand. The first graph has the shape that EquiVM run 10
measured at Lean v4.33.1 (a BFS over `getUsedConstantsAsSet`):
`Reasoning.Theory.dispatchMsg_eq_some_of_split` reaches `Classical.choice`
through Mathlib's `List.find?_congr`, its private auxiliary
`_private.Mathlib.Data.List.Find.0.List.find?_congr._proof_1_1` (the name
that run 10's evidence holds), `Classical.byContradiction` and
`Classical.propDecidable`. At v4.29.0 `List.find?_congr` is in another module
and has no classical axiom. The end-to-end checks against real Lean are
`tests/card-cause.sh` and `tests/card-body.sh`.
-/

open LeanMend

namespace CauseTest

def c (name module : String) (axioms uses : List String) (ax : Bool := false) : Const :=
  { name, module, axioms, uses, axiomName := if ax then some name else none }

def choiceAx := ["Classical.choice"]
def three := ["Classical.choice", "Quot.sound", "propext"]
/-- The auxiliary of `List.find?_congr` at Mathlib 0df444a3. -/
def aux := "_private.Mathlib.Data.List.Find.0.List.find?_congr._proof_1_1"

/-- v4.33.1: the dispatch theorem reaches `Classical.choice` through
`List.find?_congr`. A longer route to the axiom exists through `slow`. -/
def after : Side :=
  { toolchain := "v4.33.1", missing := [],
    owners := [("Reasoning.Dispatch", ⟨"EquiVM", "afb51a53"⟩),
               ("Mathlib.Data.List.Find", ⟨"mathlib", "0df444a3"⟩),
               ("Init.Classical", ⟨"Lean core", "v4.33.1"⟩), ("Init.Prelude", ⟨"Lean core", "v4.33.1"⟩)],
    consts := [
      c "D.split" "Reasoning.Dispatch" three ["D.eq", "slow"],
      c "D.eq" "Reasoning.Dispatch" three ["List.find?_congr"],
      c "slow" "Reasoning.Dispatch" three ["slow2"],
      c "slow2" "Reasoning.Dispatch" three ["slow3"],
      c "slow3" "Reasoning.Dispatch" three ["slow4"],
      c "slow4" "Reasoning.Dispatch" three ["slow5"],
      c "slow5" "Reasoning.Dispatch" three ["Classical.choice"],
      c "List.find?_congr" "Mathlib.Data.List.Find" three [aux],
      c aux "Mathlib.Data.List.Find" three ["Classical.byContradiction"],
      c "Classical.byContradiction" "Init.Classical" choiceAx ["Classical.propDecidable"],
      c "Classical.propDecidable" "Init.Classical" choiceAx ["Classical.choice"],
      c "Classical.choice" "Init.Prelude" choiceAx [] (ax := true),
      c "E.other" "Reasoning.Dispatch" three ["D.eq"]] }

/-- v4.29.0: the same declarations; `List.find?_congr` is in
`Mathlib.Data.List.Basic` with no classical axiom, and it has no
`_proof_1_1`. The classical lemmas are there, outside the closure of the
dispatch theorem: the probe gives them as lookups (`pathLookups`). -/
def base : Side :=
  { toolchain := "v4.29.0", missing := [aux],
    owners := [("Reasoning.Dispatch", ⟨"EquiVM", "1ac3d7b5"⟩),
               ("Mathlib.Data.List.Basic", ⟨"mathlib", "8a178386"⟩),
               ("Init.Classical", ⟨"Lean core", "v4.29.0"⟩), ("Init.Prelude", ⟨"Lean core", "v4.29.0"⟩)],
    consts := [
      c "D.split" "Reasoning.Dispatch" ["Quot.sound", "propext"] ["D.eq"],
      c "D.eq" "Reasoning.Dispatch" ["Quot.sound", "propext"] ["List.find?_congr"],
      c "List.find?_congr" "Mathlib.Data.List.Basic" ["propext"] [],
      c "Classical.byContradiction" "Init.Classical" choiceAx ["Classical.propDecidable"],
      c "Classical.propDecidable" "Init.Classical" choiceAx ["Classical.choice"],
      c "Classical.choice" "Init.Prelude" choiceAx [] (ax := true),
      c "E.other" "Reasoning.Dispatch" ["Quot.sound", "propext"] ["D.eq"]] }

def decl (n : String) (axioms : List String) : Decl :=
  { name := n, module := "Reasoning.Dispatch", kind := .theorem, statementHash := "", bodyHash := "", axioms }

def names : Names := Names.ofAliases ⟨[]⟩

def check (failed : IO.Ref Nat) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}{if ok then "" else s!": {detail}"}"
  unless ok do failed.modify (· + 1)

def causeName : AxiomExplanation → String
  | .cause x => x.cause.here.name
  | .notComputed _ _ r => s!"not computed: {r}"

/-- The checks of the run 10 shape: one explanation, with its path and cause. -/
def checkRun10 (failed : IO.Ref Nat) (xs : List AxiomExplanation) : IO Unit := do
  let [.cause x] := xs
    | check failed "one explanation for one added axiom" false (repr xs |>.pretty)
  check failed "the shortest path at v4.33.1 goes through List.find?_congr, not the longer route"
    (x.path.map (·.here.name) == ["D.split", "D.eq", "List.find?_congr", aux,
      "Classical.byContradiction", "Classical.propDecidable", "Classical.choice"])
    (toString (x.path.map (·.here.name)))
  check failed "the cause is List.find?_congr: the auxiliary _proof_1_1 gives its place to its owner"
    (x.cause.here.name == "List.find?_congr") x.cause.here.name
  check failed "the cause names its module and the mathlib revision at each toolchain"
    (x.cause.here == .present "List.find?_congr" "Mathlib.Data.List.Find" (some ⟨"mathlib", "0df444a3"⟩) three &&
     x.cause.there == .present "List.find?_congr" "Mathlib.Data.List.Basic" (some ⟨"mathlib", "8a178386"⟩) ["propext"])
    (repr x.cause |>.pretty)
  let otherOk := match x.otherPath with
    | .ok p => p == ["D.split", "D.eq", "List.find?_congr"]
    | .error _ => false
  check failed "the path at v4.29.0 leads to the cause" otherOk (repr x.otherPath |>.pretty)
  check failed "the change is an added axiom" (x.change == .added && x.axiom_ == "Classical.choice")

/-- A `Presence` with an owner, for a hand-built `Link` of a site test
(decision D14). `axs` is unused by `siteOf`; it exists only so the same
`Presence` builder works for `explainViolation`'s fixtures above. -/
def pr (pkg n m : String) (axs : List String := []) : Presence :=
  .present n m (some ⟨pkg, "rev"⟩) axs

/-- A `Link` of EquiVM's own module (the target package). -/
def owned (n m : String) (axs : List String := []) : Link := { here := pr "EquiVM" n m axs, there := .absent n }
/-- A `Link` of a dependency package (Mathlib). -/
def dep (n m : String) (axs : List String := []) : Link := { here := pr "mathlib" n m axs, there := .absent n }
/-- A `Link` of Lean core. -/
def core (n m : String) (axs : List String := []) : Link := { here := pr "Lean core" n m axs, there := .absent n }

/-- An `AxiomCause` built directly from a hand-written `path` and `cause`
(the site tests do not need `otherPath`, so it is a fixed error). -/
def mkCause (path : List Link) (cause : Link) (axiom_ : String := "Classical.choice")
    (change : Change := .added) : AxiomCause :=
  { axiom_, change, path, cause, otherPath := .error "not needed by a site test" }

/-- Decision D14, on hand-built paths: the site is the nearest owned
ancestor of the cause, walking from the axiom toward the declaration. -/
def checkSite (failed : IO.Ref Nat) : IO Unit := do
  -- "cause in a dependency": an owned ancestor sits between the declaration
  -- and the cause, so the site is that ancestor, not the declaration.
  let causeA := dep "Lib.congr" "Mathlib.X"
  let pathA : List Link := [owned "App.foo" "App", owned "App.bar" "App", causeA,
    dep "Lib.aux" "Mathlib.X", core "Classical.choice" "Init.Prelude"]
  check failed "cause in a dependency: the site is the nearest owned ancestor of the cause, not the declaration"
    (siteOf "EquiVM" (mkCause pathA causeA) == ("App.bar", "App"))
    (toString (siteOf "EquiVM" (mkCause pathA causeA)))
  -- "cause a generated auxiliary of a target constant": the cause itself is
  -- owned (EquiVM's own generated matcher), with another owned constant,
  -- its own generated helper, between it and the named declaration. Both
  -- are generated (`ownerNames`), so the site is the declaration they
  -- belong to, not either generated name (this is the shape of EquiVM run
  -- 10's G3, `.scratch/axiom-fix/edits.md` § Edit E3: `allocationSizes._f`
  -- and `allocationSizes.match_1` both give their place to `allocationSizes`).
  let causeB := owned "Stele.Interp.allocationSizes.match_1" "Stele.Interp"
  let pathB : List Link := [owned "Stele.Interp.allocationSizes" "Stele.Interp",
    owned "Stele.Interp.allocationSizes._f" "Stele.Interp", causeB,
    core "Nat.hasNotBit" "Init.Data.Nat.Bitwise.Basic", core "propext" "Init.Prelude"]
  check failed "cause a generated auxiliary of a target constant: the generated helper before it \
gives its place to the declaration it belongs to"
    (siteOf "EquiVM" (mkCause pathB causeB "propext") == ("Stele.Interp.allocationSizes", "Stele.Interp"))
    (toString (siteOf "EquiVM" (mkCause pathB causeB "propext")))
  -- A generated matcher downstream of a plain owned helper: `match_1`
  -- collapses to its owner even when that owner is not the site's `d`
  -- (the owner rule generalizes `pickCause`'s private-auxiliary rule to a
  -- `match_`-prefixed component, not only an underscore-prefixed one).
  let causeE := dep "Lib.congr" "Mathlib.X"
  let pathE : List Link := [owned "App.Root" "App", owned "App.Helper" "App",
    owned "App.Helper.match_1" "App", causeE, core "Classical.choice" "Init.Prelude"]
  check failed "a generated matcher of an owned helper gives its place to that helper, not the named declaration"
    (siteOf "EquiVM" (mkCause pathE causeE) == ("App.Helper", "App"))
    (toString (siteOf "EquiVM" (mkCause pathE causeE)))
  -- "a path with no owned constant" other than the declaration: the site
  -- falls back to `path[0]`, the declaration itself.
  let causeC := dep "Lib.f" "Mathlib.X"
  let pathC : List Link := [owned "App.root" "App", causeC, core "Classical.choice" "Init.Prelude"]
  check failed "a path with no owned constant between the declaration and the cause: the site is the declaration"
    (siteOf "EquiVM" (mkCause pathC causeC) == ("App.root", "App"))
    (toString (siteOf "EquiVM" (mkCause pathC causeC)))
  -- "two findings sharing one site": a second declaration whose own path
  -- also runs through `App.bar` before the same cause groups with the
  -- first; a third, with a different cause, stays a second group.
  let causeD := dep "Lib.congr" "Mathlib.X"
  let pathD : List Link := [owned "App.other" "App", owned "App.bar" "App", causeD,
    dep "Lib.aux" "Mathlib.X", core "Classical.choice" "Init.Prelude"]
  let gs := groupFindingSites "EquiVM"
    [("c-1", "App.foo", [.cause (mkCause pathA causeA)]),
     ("c-2", "App.other", [.cause (mkCause pathD causeD)]),
     ("c-3", "App.root", [.cause (mkCause pathC causeC)])]
  check failed "two findings whose paths both reach App.bar before the same cause share one FindingSite; \
the third, with a different cause, is a second group"
    (gs.map (fun g => (g.key, g.members.map (·.1))) ==
      [({ site := ("App.bar", "App"), cause := .const "Lib.congr" "Mathlib.X" .added }, ["c-1", "c-2"]),
       ({ site := ("App.root", "App"), cause := .const "Lib.f" "Mathlib.X" .added }, ["c-3"])])
    (repr (gs.map (·.key)) |>.pretty)

/-- The site on EquiVM run 10's real measured paths
(`.scratch/axiom-fix/edits.md` in the monorepo root, Lean v4.29.0 →
v4.33.1). `"EquiVM"` is the target's root package name
(`lake-manifest.json`'s own `name` field). -/
def checkRealEvidence (failed : IO.Ref Nat) : IO Unit := do
  -- G1 (38 cards, c-3 … c-40), Edit E1. This is card c-40's own path,
  -- `Reasoning.Theory.selectorDispatchMsg_eq_dispatchList` itself: every
  -- other G1 card's own path reaches this same declaration first (§ Edit
  -- E1), so all 38 share this site.
  let g1Cause := dep "List.find?_congr" "Mathlib.Data.List.Find"
  let g1Path : List Link := [owned "Reasoning.Theory.selectorDispatchMsg_eq_dispatchList" "Reasoning.Dispatch",
    g1Cause, dep "_private.Mathlib.Data.List.Find.0.List.find?_congr._proof_1_1" "Mathlib.Data.List.Find",
    core "Classical.byContradiction" "Init.Classical", core "Classical.propDecidable" "Init.Classical",
    core "Classical.choice" "Init.Prelude"]
  check failed "G1, Edit E1: the site is the dispatch theorem itself, matching decision D14 and \
.scratch/axiom-fix/edits.md § Edit E1 (38 cards)"
    (siteOf "EquiVM" (mkCause g1Path g1Cause) ==
      ("Reasoning.Theory.selectorDispatchMsg_eq_dispatchList", "Reasoning.Dispatch"))
    (toString (siteOf "EquiVM" (mkCause g1Path g1Cause)))
  -- G2 (4 cards, c-41 … c-44), Edit E2.
  let g2Cause := core "Lean.Loop.forIn" "Init.While"
  let g2Path : List Link := [owned "Stele.DiffTest.Rng.bigNat" "Stele.DiffTest.Gen",
    core "Lean.instForInLoopUnitOfMonad" "Init.While", g2Cause, core "repeatM" "Init.While",
    core "_private.Init.While.0.repeatM.impl" "Init.While", core "Classical.ofNonempty" "Init.Prelude",
    core "Classical.choice" "Init.Prelude"]
  check failed "G2, Edit E2: the site is Rng.bigNat itself, matching .scratch/axiom-fix/edits.md § Edit E2 (4 cards)"
    (siteOf "EquiVM" (mkCause g2Path g2Cause) == ("Stele.DiffTest.Rng.bigNat", "Stele.DiffTest.Gen"))
    (toString (siteOf "EquiVM" (mkCause g2Path g2Cause)))
  -- G3 (1 card, c-45), Edit E3. `allocationSizes._f` (a well-founded-
  -- recursion helper) and `allocationSizes.match_1` (the generated matcher,
  -- the cause) are both generated, so the owner rule gives both their place
  -- to `allocationSizes`, the declaration Edit E3 changed, matching
  -- `.scratch/axiom-fix/edits.md`'s "Nearest EquiVM declaration" column.
  let g3Cause := owned "Stele.Interp.allocationSizes.match_1" "Stele.Interp"
  let g3Path : List Link := [owned "Stele.Interp.allocationSizes" "Stele.Interp",
    owned "Stele.Interp.allocationSizes._f" "Stele.Interp", g3Cause,
    core "Nat.hasNotBit" "Init.Data.Nat.Bitwise.Basic", core "propext" "Init.Prelude"]
  check failed "G3, Edit E3: the site is allocationSizes itself, matching .scratch/axiom-fix/edits.md § Edit E3"
    (siteOf "EquiVM" (mkCause g3Path g3Cause "propext") == ("Stele.Interp.allocationSizes", "Stele.Interp"))
    (toString (siteOf "EquiVM" (mkCause g3Path g3Cause "propext")))

def run : IO Nat := do
  let failed ← IO.mkRef 0
  checkSite failed
  checkRealEvidence failed
  checkRun10 failed <|
    explainViolation names base after (decl "D.split" ["Quot.sound", "propext"]) (decl "D.split" three)
  -- A constant that exists only at v4.33.1 is a difference: with no owner
  -- on the path, the auxiliary itself is the cause.
  let noOwner := { after with consts := after.consts.map fun k =>
    if k.name == "D.eq" then { k with uses := [aux] } else k }
  let ys := explainViolation names base noOwner (decl "D.split" ["Quot.sound", "propext"]) (decl "D.split" three)
  check failed "an auxiliary that exists at one toolchain only, with no owner on the path, is the cause"
    (ys.map causeName == [aux]) (toString (ys.map causeName))
  -- A removed axiom: the path is at the old toolchain.
  let zs := explainViolation names after base (decl "D.split" three) (decl "D.split" ["Quot.sound", "propext"])
  let removedOk := match zs with
    | [.cause x] => x.change == .removed && x.cause.here.name == "List.find?_congr"
    | _ => false
  check failed "a removed axiom has its path at the old toolchain" removedOk (repr zs |>.pretty)
  -- No data for the declaration: stated, not guessed.
  let ws := explainViolation names base after (decl "Gone" []) (decl "Gone" choiceAx)
  check failed "a declaration with no data has its cause not computed, with the reason"
    (ws.map causeName == ["not computed: at v4.33.1 the probe's data has no path from Gone to Classical.choice"])
    (toString (ws.map causeName))
  -- Two declarations with one cause, and one with another: two groups.
  let g1 := explainViolation names base after (decl "D.split" ["Quot.sound", "propext"]) (decl "D.split" three)
  let g2 := explainViolation names base after (decl "E.other" ["Quot.sound", "propext"]) (decl "E.other" three)
  let g3 := explainViolation names base noOwner (decl "D.split" ["Quot.sound", "propext"]) (decl "D.split" three)
  let gs := groupCauses [("c-1", "D.split", g1), ("c-2", "E.other", g2), ("c-3", "X", g3)]
  check failed "two declarations that share List.find?_congr form one group; the other cause is a second group"
    (gs.map (fun g => (g.key, g.members.map (·.1))) ==
      [(.const "List.find?_congr" "Mathlib.Data.List.Find" .added, ["c-1", "c-2"]),
       (.const aux "Mathlib.Data.List.Find" .added, ["c-3"])])
    (repr (gs.map (·.key)) |>.pretty)
  -- The names at v4.33.1 that v4.29.0 must report: every name on the path.
  check failed "pathLookups names every constant of the new path"
    (pathLookups after [("D.split", "Classical.choice")] names.toBase ==
      ["D.split", "D.eq", "List.find?_congr", aux,
       "Classical.byContradiction", "Classical.propDecidable", "Classical.choice"])
  check failed "the owner of a private auxiliary is the name after `_private.<module>.0.`, or the private name"
    (ownerNames aux == ["List.find?_congr", "_private.Mathlib.Data.List.Find.0.List.find?_congr"] &&
     ownerNames "_private.Init.While.0.repeatM.Pred" == [] && ownerNames "Classical.choice" == [])
    (toString (ownerNames aux))
  -- Behavior: run 10's EVM.Word.toBytesLEWithSizeProof, lines 33 and 34 of
  -- EVM/Types.lean, inside the `by` block of `hb`.
  let pre := "  ⟨b, by\n    have hb : b.length ≤ 32 := by\n      have ha : v < 2 ^ 256 := by\n" ++
    "        simp [size, toNat]\n      simpa [b, BE] using le ha\n    exact hb⟩"
  let post := "  ⟨b, by\n    have hb : b.length ≤ 32 := by\n      have ha : v < 2 ^ 256 := by\n" ++
    "        simpa [size, toNat] using v.isLt\n      simpa [b, BE, toNat] using le ha\n    exact hb⟩"
  -- The whole `by` block after `⟨b, ` is a proof (a subtype's property).
  let proofOf (s : String) (start : Nat) : List (Nat × Nat) :=
    [(start + 6, start + s.utf8ByteSize - 1)]
  let b : Body := { text := pre, start := 1000, proofs := proofOf pre 1000 }
  let a : Body := { text := post, start := 2000, proofs := proofOf post 2000 }
  let ch := bodyChange b a
  check failed "the run 10 body change is one hunk of two lines" (ch.hunks.map (fun h => (h.beforeLine, h.removed.length, h.added.length)) == [(3, 2, 2)])
    (repr ch.hunks |>.pretty)
  check failed "the run 10 body change lies in a proof only" ch.proofOnly (repr ch |>.pretty)
  -- A `by` block that computes a number is no proof: the probe gives no range.
  let d1 : Body := { text := ":= by exact 2", start := 0, proofs := [] }
  let d2 : Body := { text := ":= by exact 3", start := 0, proofs := [] }
  check failed "a change in a by block that computes data is not in a proof only" (!(bodyChange d1 d2).proofOnly)
  check failed "the changed bytes of `2` → `3` are the one digit"
    ((bodyChange d1 d2).hunks.map (·.afterSpan) == [(12, 13)]) (repr (bodyChange d1 d2).hunks |>.pretty)
  -- `⟨` is 3 bytes, so `h` is bytes 6 to 7 and `hx` 6 to 8. From `h` to
  -- `hx` the old side's change is the point at byte 7, the end of `h`, and
  -- the new side's change `x` lies inside the proof `hx`.
  let p1 : Body := { text := "⟨n, h⟩", start := 0, proofs := [(6, 7)] }
  let p2 : Body := { text := "⟨n, hx⟩", start := 0, proofs := [(6, 8)] }
  check failed "a proof that becomes a longer proof is a change in a proof only" (bodyChange p1 p2).proofOnly
    (repr (bodyChange p1 p2) |>.pretty)
  -- Data after a proof: the old point is at the end of `h`, but the new
  -- bytes `, x` lie in no proof.
  let p3 : Body := { text := "⟨n, h, x⟩", start := 0, proofs := [(6, 7)] }
  check failed "bytes added just after a proof, outside it, are not in a proof only" (!(bodyChange p1 p3).proofOnly)
    (repr (bodyChange p1 p3) |>.pretty)
  check failed "equal bodies give no hunk and no proof-only verdict"
    ((bodyChange d1 d1).hunks.isEmpty && !(bodyChange d1 d1).proofOnly)
  return ← failed.get

end CauseTest
