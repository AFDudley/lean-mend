/-! S4 (`docs/parallel.md` P14-P16): `tests/speculate.sh` runs lean-mend with
the rules in `rules/`, in file-name (rule) order. The first two rules leave
the site open. The third rule fixes the site. The run speculates all three
candidates at the same time, and the Core must still accept the third
candidate, in rule order (P15), not the first to finish.

A test barrier, not the time each candidate takes, sets the order of finish.
The third candidate runs `barrierMark "fast-fix"`, which records the pid of
its own probe process. The first two candidates run
`barrierAwaitStopped "fast-fix"`, which waits until that process stops. The
driver stops a nested probe only after it records the candidate's
`finishedAt` (`onProbe` in `LeanMend/Shell/Driver.lean`). So the third
candidate finishes first at any host load.

`tests/speculate.sh` sets `FIXTURE_BARRIER_DIR` only for the `--speculate 3`
run. The sequential run attempts the first two candidates before the third,
so there the barrier must be off. -/

/-! The test barrier. The same block is in each fixture module that uses a
barrier: `tests/fixtures/speculate/App.lean`, `tests/fixtures/fleet/ModA.lean`
and `ModB.lean`, `tests/fixtures/dataflow/Slow.lean` and `Dep.lean`, and
`tests/fixtures/probe-bound/ModA.lean`, `ModB.lean` and `ModC.lean`, and
their copies in `expected/`. Keep the copies equal. A fixture module cannot
import a shared file: lean-mend mends every `.lean` file of the target, so a
shared module would change the module lists that the runners check.

A candidate calls the barrier with `#eval` commands after its declaration.
The block uses only `Init`, so the fixture imports nothing more. -/

/-- The marker directory of the test barrier: the environment variable
`FIXTURE_BARRIER_DIR`. When the variable is not set, every barrier call does
nothing. -/
def barrierDir : IO (Option System.FilePath) :=
  return (← IO.getEnv "FIXTURE_BARRIER_DIR").map System.FilePath.mk

/-- Wait until `ready` is true. The wait checks every 50 ms, because a file
gives no event to wait on. The wait fails after 600 s, so a broken barrier
fails its test and does not hang it. -/
def barrierWait (what : String) (ready : IO Bool) : IO Unit := do
  let start ← IO.monoMsNow
  repeat
    if ← ready then return
    if (← IO.monoMsNow) - start > 600000 then
      throw <| IO.userError s!"barrier: {what} did not occur in 600 s"
    IO.sleep 50

/-- Write the pid of this `lean` process to the marker `n`. The write goes
through a temporary file and a rename, so a reader never sees a partial pid.
A marker that exists keeps its first pid. -/
def barrierMark (n : String) : IO Unit := do
  let some dir ← barrierDir | return
  let path := dir / n
  if ← path.pathExists then return
  let tmp := dir / (n ++ ".tmp")
  IO.FS.writeFile tmp (toString (← IO.Process.getPID))
  IO.FS.rename tmp path

/-- Wait until each marker in `ns` exists. -/
def barrierAwait (ns : List String) : IO Unit := do
  let some dir ← barrierDir | return
  for n in ns do
    barrierWait s!"the marker {n}" (dir / n).pathExists

/-- Wait until the marker `n` exists and the process whose pid it holds
stopped. -/
def barrierAwaitStopped (n : String) : IO Unit := do
  let some dir ← barrierDir | return
  let path := dir / n
  barrierWait s!"the stop of the process of the marker {n}" do
    unless ← path.pathExists do return false
    let pid := (← IO.FS.readFile path).trimAscii.toString
    return !(← System.FilePath.pathExists s!"/proc/{pid}")

theorem foo : True := by
  exact unknownHead
