/-! The base text of a theorem whose statement uses `zap` as an identifier
(tests/statement-change.sh). In the environment of a batch that also holds
`App.Tok`, `zap` is a token, and the statement does not parse. Before the
shell read such a module again alone, the certificate had no row for the
theorem, so the bump commit's token change was no finding. On EquiVM, the
statement of `UniswapV2Pair.evalExpr_constructor_thisWord`
(`… addressAsUint256 this …`) does not parse in an environment that holds
`Stele.Notation`, for the same reason. -/
namespace App

theorem zap_refl (zap : Nat) : zap = zap := rfl

end App
