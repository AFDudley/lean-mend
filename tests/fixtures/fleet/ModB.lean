/-! Paired with `ModA.lean` for `tests/fleet.sh`: an independent module with
its own break. `ModA` and `ModB` do not import each other, so both mend at
the same time. `ModB`'s fix marks its start and waits until `ModA`'s attempt
starts (see `ModA.lean`). -/

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

theorem fooB : True := by
  exact unknownHeadB
