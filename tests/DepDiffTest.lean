import LeanMend.Core.DepDiff

/-!
# The dependency diff (`LeanMend.Core.DepDiff`, `docs/static-diff.md` § 1)

Pure checks of `depDiff` over hand-built rows, the shape
`tests/dep-diff.sh` exercises end to end against the real probe (the same
`Dep.f_congr`/`Dep.f_pos` shape, `docs/static-diff.md` § 1's run 10 table).
-/

open LeanMend

namespace DepDiffTest

def row (name module kind : String) (axioms : List String) (bodyHash : String)
    (package rev : String) : DepRow :=
  { const := { name, module, kind, axioms, bodyHash := some bodyHash, uses := [] },
    owner := ⟨package, rev⟩ }

def check (failed : IO.Ref Nat) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  IO.println s!"{if ok then "ok  " else "FAIL"} {name}{if ok then "" else s!": {detail}"}"
  unless ok do failed.modify (· + 1)

def run : IO Nat := do
  let failed ← IO.mkRef 0
  -- `Dep.f_congr`: a theorem, no axiom at the before side, `Classical.choice`
  -- at the after side, in the same module. `Dep.f_pos`: the same axiom
  -- gain, and a module move. `Dep.usesProof`: a def, unchanged at both
  -- sides.
  let before := [row "Dep.f_congr" "Dep.Basic" "theorem" [] "#" "dep" "v1",
                 row "Dep.f_pos" "Dep.Basic" "theorem" [] "#" "dep" "v1",
                 row "Dep.usesProof" "Dep.Basic" "def" [] "(lam # #)" "dep" "v1"]
  let after := [row "Dep.f_congr" "Dep.Basic" "theorem" ["Classical.choice"] "#" "dep" "v2",
                row "Dep.f_pos" "Dep.Pos" "theorem" ["Classical.choice"] "#" "dep" "v2",
                row "Dep.usesProof" "Dep.Basic" "def" [] "(lam # #)" "dep" "v2"]
  let es := depDiff before after
  check failed "the diff has exactly two entries: f_congr and f_pos, not usesProof"
    ((es.map (·.name)) == ["Dep.f_congr", "Dep.f_pos"]) (repr (es.map (·.name)) |>.pretty)
  let congr := es.find? (·.name == "Dep.f_congr")
  check failed "f_congr's kind is an axiom gain, with no removal"
    (congr.map (·.kind) == some (.axioms ["Classical.choice"] [])) (repr (congr.map (·.kind)) |>.pretty)
  check failed "f_congr's module is Dep.Basic at both sides"
    (congr.bind (·.before.map (·.const.module)) == some "Dep.Basic" &&
     congr.bind (·.after.map (·.const.module)) == some "Dep.Basic")
  let pos := es.find? (·.name == "Dep.f_pos")
  check failed "f_pos's kind is an axiom gain"
    (pos.map (·.kind) == some (.axioms ["Classical.choice"] [])) (repr (pos.map (·.kind)) |>.pretty)
  check failed "f_pos moves from Dep.Basic to Dep.Pos"
    (pos.bind (·.before.map (·.const.module)) == some "Dep.Basic" &&
     pos.bind (·.after.map (·.const.module)) == some "Dep.Pos")
  -- A lost axiom, and a presence at one side only.
  let onlyBase := [row "Dep.dropped" "Dep.Basic" "def" ["propext"] "#" "dep" "v1"]
  let onlyAfter := []
  let gone := depDiff onlyBase onlyAfter
  check failed "a constant that exists at the before side only is onlyBefore"
    (gone == [{ name := "Dep.dropped", kind := .onlyBefore, before := onlyBase.head?, after := none }])
    (repr gone |>.pretty)
  let appears := depDiff onlyAfter (onlyBase.map fun r => { r with const := { r.const with axioms := [] } })
  check failed "a constant that exists at the after side only is onlyAfter"
    (appears.map (·.kind) == [.onlyAfter]) (repr (appears.map (·.kind)) |>.pretty)
  -- An unchanged axiom set with a different proof-erased body, on a `def`.
  let bodyBefore := [row "Dep.g" "Dep.Basic" "def" [] "(lit a)" "dep" "v1"]
  let bodyAfter := [row "Dep.g" "Dep.Basic" "def" [] "(lit b)" "dep" "v2"]
  check failed "an unchanged axiom set with a different erased body is a body-changed entry, for a def"
    ((depDiff bodyBefore bodyAfter).map (·.kind) == [.body])
  -- The same body-hash difference, on a `theorem`: proof irrelevance means
  -- `depDiff` never reads a theorem's body hash, so it gives no entry.
  let thmBefore := [row "Dep.h" "Dep.Basic" "theorem" [] "(lit a)" "dep" "v1"]
  let thmAfter := [row "Dep.h" "Dep.Basic" "theorem" [] "(lit b)" "dep" "v2"]
  check failed "an unchanged axiom set with a different body hash on a theorem is no entry"
    (depDiff thmBefore thmAfter == [])
  -- Identical rows: no entry.
  check failed "identical rows give no entry" (depDiff before before == [])
  return ← failed.get

end DepDiffTest
