/-! `tests/cap-stop.sh` (`docs/parallel.md` P24, § The memory limit): the
probe of this module writes the text of the `lean -M` cap to its stderr and
then does not exit. On 2026-11-06 a run with `import Lean` fixtures (the
branch `speculate-barrier`) saw probes that wrote this text, and the run then
made no progress for 3600 s.

The rule's candidate adds `#eval capThenHold` after the theorem, so only the
probe runs it: the runner's builds elaborate the module without the
candidate. The marker directory is the environment variable `CAP_STOP_DIR`.
The block uses only `Init`, so the module imports nothing. -/

/-- The marker directory `CAP_STOP_DIR`. -/
def markerDir : IO System.FilePath := do
  let some d ← IO.getEnv "CAP_STOP_DIR" | throw <| IO.userError "CAP_STOP_DIR is not set"
  return d

/-- The text that the Lean runtime writes when a process passes its `-M`
cap (`check_memory`; v4.29.0, v4.33.1 and v4.35.0). -/
def capText : String :=
  "excessive memory consumption detected at 'interpreter' (potential solution: increase memory consumption threshold)"

/-- Wait until the probe of `Held` wrote its marker, so that probe is live
when this one writes the cap text. Then write the marker `capped` and the cap
text to the process's own stderr. `#eval` sends the output of `IO.eprintln`
to a message, so the text goes to `/proc/self/fd/2`. Then wait 600 s. The
wait has a bound, so a driver that does not end this probe fails the runner
by time and does not hang it. -/
def capThenHold : IO Unit := do
  let dir ← markerDir
  let start ← IO.monoMsNow
  repeat
    if ← (dir / "held").pathExists then break
    if (← IO.monoMsNow) - start > 600000 then
      throw <| IO.userError "the marker held did not occur in 600 s"
    IO.sleep 50
  IO.FS.writeFile (dir / "capped") (toString (← IO.Process.getPID))
  IO.FS.withFile "/proc/self/fd/2" .append fun h => do
    h.putStrLn capText
    h.flush
  IO.sleep 600000

theorem fooCapped : True := by
  exact unknownHeadCapped
