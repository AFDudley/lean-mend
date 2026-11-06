/-! The base text of a theorem whose statement uses a `local notation` of the
same file (tests/statement-change.sh). The module does not export a local
notation, so a parse with the environment of the imports and the module does
not parse the statement. Before the probe read the file's own commands, the
certificate had no row for the theorem, so the bump commit's token change
was no finding. -/
namespace App

local notation:70 a:71 " ⊠ " b:71 => a * b + 1

theorem local_product : 2 ⊠ 3 = 7 := rfl

end App
