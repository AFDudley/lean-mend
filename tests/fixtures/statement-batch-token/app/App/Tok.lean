/-! A module that makes `zap` a token (tests/statement-change.sh). `App.T`
does not import it, so `zap` is an identifier in `App.T`. The probe's
`decls-batch` imports both modules into one environment, where `zap` is a
token, as `Stele.Notation` makes `this` a token on EquiVM. -/
syntax "zap" : term
