/-! `tests/cap-stop.sh` (`docs/parallel.md` P24, § The memory limit): the
probe of this module is live and gives no reply when the probe of `Capped`
writes the cap text. It does not write the cap text, so only the stop of the
run can end it.

The rule's candidate adds `#eval holdProbe` after the theorem, so only the
probe runs it: the runner's builds elaborate the module without the
candidate. The marker directory is the environment variable `CAP_STOP_DIR`.
The block uses only `Init`, so the module imports nothing. -/

/-- Write the pid of this `lean` process to the marker `held` in
`CAP_STOP_DIR`, then wait 600 s. The write goes through a temporary file and
a rename, so a reader never sees a partial pid. The wait has a bound, so a
driver that does not end this probe fails the runner by time and does not
hang it. -/
def holdProbe : IO Unit := do
  let some d ← IO.getEnv "CAP_STOP_DIR" | throw <| IO.userError "CAP_STOP_DIR is not set"
  let dir : System.FilePath := d
  IO.FS.writeFile (dir / "held.tmp") (toString (← IO.Process.getPID))
  IO.FS.rename (dir / "held.tmp") (dir / "held")
  IO.sleep 600000

theorem fooHeld : True := by
  exact unknownHeadHeld
