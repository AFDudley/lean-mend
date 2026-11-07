import LeanMend.Core.Run
import Std.Data.HashSet

/-!
# Module-graph order

Brief item 1: build in module-dependency order. `topoOrder` puts every module
after the modules it imports. Imports of modules outside the target (Lean,
Mathlib) are ignored: Lake builds those as dependencies. A cycle is a refusal.
Pure; see `docs/machine.md` § Operands.
-/

namespace LeanMend

/-- Modules in an order where each one follows its target-internal imports.
Kahn's algorithm. Each round places at least one module or refuses, so
`mods.length + 1` rounds are enough. -/
def topoOrder (mods : List Module) : Except Refusal (List Module) :=
  let names := mods.map (·.name)
  let internal (m : Module) := m.imports.filter (names.contains ·)
  let rec go : Nat → List Module → List String → List Module → Except Refusal (List Module)
    | _, [], _, acc => .ok acc.reverse
    | 0, rest, _, _ =>
      .error (.observationMismatch s!"import cycle among {rest.map (·.name)}")
    | fuel + 1, rest, done, acc =>
      let (ready, waiting) := rest.partition fun m => (internal m).all (done.contains ·)
      if ready.isEmpty then
        .error (.observationMismatch s!"import cycle among {rest.map (·.name)}")
      else go fuel waiting (done ++ ready.map (·.name)) (ready.reverse ++ acc)
  go (mods.length + 1) mods [] []

/-- Every module of `mods` that `n` imports, directly or through other
modules of `mods`, in `mods` order. `mods` must be in `topoOrder` order: a
module then comes after every module it imports, so one pass from the end
visits each importer before its imports. A module's followed-rule snapshot
is the body rules of these modules (`docs/parallel.md` P22). -/
def importClosure (mods : List Module) (n : String) : List String :=
  let reach := mods.foldr (init := ({n} : Std.HashSet String)) fun m acc =>
    if acc.contains m.name then m.imports.foldl (·.insert ·) acc else acc
  (mods.filter fun m => m.name != n && reach.contains m.name).map (·.name)

end LeanMend
