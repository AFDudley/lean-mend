import App.G

/-! An importer of `App.g` (`docs/machine.md` § Acceptance): its own path
to the cause runs through `App.g`, D14's own site. Condition 1's edit can
change what `App.g` computes (it is a `def`), so acceptance needs this
module rebuilt too — "the importers that use a changed declaration"
(decision D15). -/
namespace App

theorem useG : g = g := rfl

end App
