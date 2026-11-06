/-! `tests/probe-bound.sh` (`docs/parallel.md` P24): one of four independent
modules, each with one break. The first candidate of the rule keeps the break,
so the Core rejects it. The second candidate fixes the break and adds a slow
decided count. So each module holds its probe for two attempts, and the four
mends overlap when the memory limit admits them.

The reference case asserts that more than 2 probes are live at one time. A
test barrier, not the time each attempt takes, makes that true. In `ModA`,
`ModB` and `ModC`, the first candidate runs `barrierMark` with the module's
own name and then `barrierAwait ["a", "b", "c"]`. So the three probes are live
together when the last of the three marks occurs, at any host load.
`tests/probe-bound.sh` sets `FIXTURE_BARRIER_DIR` only for the reference case.
The bounded and speculate cases admit fewer than 3 probes at once, so there
the barrier would not end. -/

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

set_option maxRecDepth 1000000

/-- A plain recursive count, not one of Lean's accelerated `Nat` operations.
Deciding that the count of a large `n` equals `n` takes the kernel time and
memory. -/
def slowCountA : Nat → Nat
  | 0 => 0
  | n + 1 => slowCountA n + 1

theorem fooA : True := by
  exact unknownHeadA
