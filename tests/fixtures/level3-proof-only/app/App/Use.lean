import App.T

/-! An importer of `App.t` (`docs/machine.md` § Acceptance): its own path
to the cause runs through `App.t`, D14's own site, so one repair at the
site closes this finding too, with no rebuild of this module. -/
namespace App

theorem useT : (1 : Nat) + 1 = 2 := t

end App
