/-! The bump commit's text: the statement of `local_product` differs from
the base in one token, `3` changed to `4` and the result to `9`. The
certificate finds a changed statement, and the run halts. -/
namespace App

local notation:70 a:71 " ⊠ " b:71 => a * b + 1

theorem local_product : 2 ⊠ 4 = 9 := rfl

end App
