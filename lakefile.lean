import Lake

open System Lake DSL

package LeanMend where
  testDriver := "tests"
  version := v!"0.1.0"

/-- `Shell/Target.lean` embeds this file's text at compile time
(`include_str "../../probe/Probe.lean"`), which Lake's import analysis
does not see: editing this file alone does not change `Target.lean`'s
own source, so a plain `lake build` can silently keep a stale compiled
probe with the OLD embedded text (measured: `strings` on the built
binary showed no trace of an edit made minutes earlier, no error, no
warning). `input_file` tracks this file's own hash as a target, and
`LeanMend`'s `needs` below makes every module of the library depend on
it, so a change here forces `Target.lean` (and anything that imports
it) to re-elaborate. `tests/probe-source-tracked.sh` checks this
directly: edit this file, `lake build`, and `strings` the binary for
the edit. -/
input_file probeSrc where
  path := "probe/Probe.lean"
  text := true

@[default_target] lean_lib LeanMend where
  needs := #[`@/probeSrc]

lean_lib Tests where
  srcDir := "tests"
  roots := #[`Tour, `ClassifyTest, `ParseTest, `OpsTest, `CauseTest, `FindingMendingTest, `DepDiffTest, `GenAuxTest]

lean_exe tests where
  srcDir := "tests"
  root := `TestMain

lean_exe «lean-mend» where root := `Main
