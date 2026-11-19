import Std.Data.HashMap
import Std.Sync.Mutex
import Init.Data.Queue
import LeanMend.Core.Sched
import LeanMend.Shell.Parse
import LeanMend.Shell.Target

/-!
# The memory gate

The shell part of the memory limit of a run (`docs/parallel.md` P17, P24;
the pure part is `Core/Sched.lean`). The gate charges each running work item
its estimate, measures the private resident memory of the driver and every
process below it from `/proc`, and admits one probe at a time by `admits`. A
request that `admits` refuses waits in a queue, in request order. The gate
checks the queue again when a probe stops (`release`), when a build ends
(`spawn`), and when the driver's replay frees plans (`recheck`). The wait is
on those events: there is no poll, no sleep and no timeout.

The gate also knows every live probe of the run, so it ends them when the
run stops (`stop`).
-/

namespace LeanMend.Shell

open System (FilePath)

/-- The text of a `/proc` file, or `none` when its process ended between the
listing of `/proc` and the read: a process that ended holds no memory. -/
def readProc (p : FilePath) : IO (Option String) := do
  try some <$> IO.FS.readFile p
  catch
    | .noFileOrDirectory .. => pure none
    | .noSuchThing .. => pure none
    | e => throw e

/-- The parent of every process, from `/proc/<pid>/stat`. -/
def procParents : IO (List (Nat × Nat)) := do
  let mut acc := []
  for e in ← FilePath.readDir "/proc" do
    let some pid := e.fileName.toNat? | continue
    let some stat ← readProc (e.path / "stat") | continue
    acc := (pid, ← parseOrThrow s!"/proc/{pid}/stat" (Parse.statParent stat)) :: acc
  pure acc

/-- The private resident memory of one process (`Parse.privateRss`). -/
def procPrivate (pid : Nat) : IO KiB := do
  let some status ← readProc s!"/proc/{pid}/status" | pure ⟨0⟩
  parseOrThrow s!"/proc/{pid}/status" (Parse.privateRss status)

/-- The private resident memory of `root` and every process below it. -/
def treePrivate (parents : List (Nat × Nat)) (root : Nat) : IO KiB := do
  let mut sum := 0
  for p in processTree parents root do
    sum := sum + (← procPrivate p).val
  pure ⟨sum⟩

/-- What the gate charged and measured when it admitted one probe: the
ledger records it in the probe's `probeStart` line (`docs/parallel.md` P24). -/
structure Admission where
  ticket : Nat
  limit : KiB
  /-- `Load.charged`: the driver plus the charges of the running work and of
  the new probe. -/
  charged : KiB
  /-- `Load.measured`: the measured tree plus the growth left to each live
  probe plus the charge of the new probe. -/
  measured : KiB
  /-- The measured private memory of the whole tree at the admission. -/
  tree : KiB
  /-- The measured private memory of the driver process alone. -/
  driver : KiB
  /-- The probes that were live before this one. -/
  live : Nat
  /-- The other work that ran at the admission (`GateState.others`). -/
  others : Nat
  deriving Nonempty

/-- The ledger fields of an admission. -/
def Admission.fields (a : Admission) : List (String × Lean.Json) :=
  [("limitKiB", Lean.toJson a.limit.val), ("chargedKiB", Lean.toJson a.charged.val),
   ("measuredKiB", Lean.toJson a.measured.val), ("treeKiB", Lean.toJson a.tree.val),
   ("driverKiB", Lean.toJson a.driver.val), ("liveProbes", Lean.toJson a.live),
   ("otherWork", Lean.toJson a.others)]

structure GateState where
  next : Nat := 0
  /-- Every live probe by ticket: its session, or `none` before its process
  starts. -/
  live : Std.HashMap Nat (Option ProbeSession) := {}
  /-- The running work that is not a probe: the module builds (`Gate.spawn`). -/
  others : Nat := 0
  /-- The requests that wait, in request order. A request gets `none` when
  the run stopped (`Gate.stop`). -/
  waiters : Std.Queue (IO.Promise (Option Admission)) := .empty
  /-- The run stopped (`Gate.stop`): the gate admits no more probes. -/
  stopped : Bool := false

instance : Nonempty GateState := ⟨{}⟩

/-- The memory gate of one run. -/
structure Gate where
  limit : KiB
  /-- The charge of one work item (`workEstimate`). -/
  estimate : KiB
  /-- The driver's own pid: the root of the measured tree. -/
  driver : UInt32
  state : Std.Mutex GateState

def Gate.new (limit estimate : KiB) : IO Gate := do
  pure { limit, estimate, driver := ← IO.Process.getPID, state := ← Std.Mutex.new {} }

/-- Measure the tree, and admit one probe if the run did not stop and
`admits` allows it. Runs with the gate's lock held. -/
def Gate.tryAdmit (g : Gate) : Std.AtomicT GateState IO (Option Admission) := do
  let st ← get
  if st.stopped then return none
  let parents ← procParents
  let tree ← treePrivate parents g.driver.toNat
  let driver ← procPrivate g.driver.toNat
  let probes ← st.live.toList.mapM fun (_, s?) => s?.mapM fun s => treePrivate parents s.child.pid.toNat
  let load : Load := { driver, tree, probes, others := st.others }
  unless admits g.limit g.estimate load do return none
  set { st with next := st.next + 1, live := st.live.insert st.next none }
  pure (some { ticket := st.next, limit := g.limit, charged := load.charged g.estimate,
               measured := load.measured g.estimate, tree, driver, live := probes.length,
               others := st.others })

/-- Request one probe. The promise resolves at the admission: at once, when
no request waits and `admits` allows it, or else at a later `release` or
`recheck`, in request order. It resolves to `none` when the run stopped
(`stop`). -/
def Gate.acquire (g : Gate) : IO (IO.Promise (Option Admission)) := do
  let p ← IO.Promise.new
  let now ← g.state.atomically do
    let st ← get
    if st.stopped then return some none
    if st.waiters.isEmpty then
      if let some a ← g.tryAdmit then return some (some a)
    modify fun st => { st with waiters := st.waiters.enqueue p }
    pure none
  if let some a := now then p.resolve a
  pure p

/-- Request one probe with no wait: `none` when a request waits, when
`admits` refuses, or when the run stopped. A speculative round uses it for
its nested probes. -/
def Gate.tryAcquire (g : Gate) : IO (Option Admission) :=
  g.state.atomically do
    if (← get).waiters.isEmpty then g.tryAdmit else pure none

/-- Admit the waiting requests, in request order, while `admits` allows it.
Returns the promises to resolve, with their admissions. Each call admits
one request or stops, and the queue is finite. -/
partial def Gate.admitWaiting (g : Gate) :
    Std.AtomicT GateState IO (List (IO.Promise (Option Admission) × Admission)) := do
  let some (p, rest) := (← get).waiters.dequeue? | return []
  let some a ← g.tryAdmit | return []
  modify fun st => { st with waiters := rest }
  return (p, a) :: (← g.admitWaiting)

/-- Check the queue again: a task of the schedule ended, so its memory is
free. -/
def Gate.recheck (g : Gate) : IO Unit := do
  for (p, a) in ← g.state.atomically g.admitWaiting do p.resolve (some a)

/-- The probe of `ticket` started, as the session `s`. When the run stopped
before this call (`stop`), the gate ends the probe at once, so `stop` misses
no probe. -/
def Gate.started (g : Gate) (ticket : Nat) (s : ProbeSession) : IO Unit := do
  let stopped ← g.state.atomically do
    let st ← get
    set { st with live := st.live.insert ticket (some s) }
    pure st.stopped
  if stopped then probeServeKill s

/-- The run stopped (fail fast, `docs/parallel.md` P24): admit no more
probes, give `none` to every request that waits, and end every live probe
(`probeServeKill`). A task that waits for a reply of a live probe then reads
end of file and ends with an error, so every task of the schedule ends. Only
the first call acts: a probe that starts later ends in `started`. -/
def Gate.stop (g : Gate) : IO Unit := do
  let ended ← g.state.atomically do
    let st ← get
    if st.stopped then return none
    set { st with stopped := true, waiters := .empty }
    pure (some (st.live.toList.filterMap (·.2), st.waiters.toArray))
  let some (live, waiters) := ended | return
  for p in waiters do p.resolve none
  for s in live do probeServeKill s

/-- The probe of `ticket` stopped: free its place and check the queue. -/
def Gate.release (g : Gate) (ticket : Nat) : IO Unit := do
  g.state.atomically do modify fun st => { st with live := st.live.erase ticket }
  g.recheck

/-- Start `act`, work of the schedule that is not a probe (a module build),
as a task. The gate counts it as running work from now until it ends, so
`admits` does not count the schedule as idle. When it ends, its memory is
free, so the gate checks the queue again. -/
def Gate.spawn {α} (g : Gate) (act : IO α) : IO (Task (Except IO.Error α)) := do
  g.state.atomically do modify fun st => { st with others := st.others + 1 }
  IO.asTask (prio := .dedicated) do
    try act
    finally
      g.state.atomically do modify fun st => { st with others := st.others - 1 }
      g.recheck

/-- The kernel limit on the whole process tree (`docs/parallel.md` P24): a
cgroup v2 child of the driver's own cgroup, with `memory.max` at the run's
limit, or the reason that the host gives none. -/
inductive TreeLimit where
  | none (reason : String)
  | cgroup (path : FilePath) (max : KiB)

def TreeLimit.json : TreeLimit → Lean.Json
  | .none reason => Lean.Json.mkObj [("mechanism", "none"), ("reason", Lean.toJson reason)]
  | .cgroup path max => Lean.Json.mkObj
    [("mechanism", "cgroup"), ("path", Lean.toJson path.toString), ("memoryMaxKiB", Lean.toJson max.val)]

/-- `p` opens for writing. The check writes nothing. -/
def writable (p : FilePath) : IO Bool := do
  try
    discard <| IO.FS.Handle.mk p .append
    pure true
  catch
    | .permissionDenied .. => pure false
    | e => throw e

/-- `txt` lists `name` among its space-separated controllers.
`cgroup.controllers` and `cgroup.subtree_control` share this format. -/
def controllerListed (txt : String) (name : String) : Bool :=
  (txt.splitOn " ").any (·.trimAscii.toString == name)

/-- A write of `+name` to `dir`'s `cgroup.subtree_control` will succeed once
`pid` leaves `dir` for a child cgroup. Two cases give success.

First, `dir` already lists `name` as enabled. The kernel then treats the
write as a no-op (`cgroup_subtree_control_write`). It skips the task check
below.

Second, `dir` holds no task besides `pid`. This is cgroup v2's No Internal
Process Constraint (kernel docs `admin-guide/cgroup-v2.rst` § 2-4-4). The
kernel refuses to enable a domain controller on a non-root cgroup that
still has a task of its own. `dir`, inside a container, is not cgroup v2's
real root. A cgroup namespace changes only the displayed path
(`/proc/self/cgroup` reads `0::/`). It does not move `dir` in the real
tree. A container's own init process (`podman run --init`) never leaves
`dir`. So this check fails there every time, and the later
`cgroup.subtree_control` write fails with EBUSY. Measured by `strace` on a
real gate container run: the Lean runtime did not surface that EBUSY as a
thrown exception, so the run went on and failed later, on `memory.max`,
with a misleading EACCES. -/
def canEnableController (dir : FilePath) (name : String) (pid : UInt32) : IO Bool := do
  let subtreeControl ← IO.FS.readFile (dir / "cgroup.subtree_control")
  if controllerListed subtreeControl name then
    pure true
  else
    let procs ← IO.FS.readFile (dir / "cgroup.procs")
    let others := (procs.splitOn "\n").filterMap (·.trimAscii.toString.toNat?)
      |>.filter (· ≠ pid.toNat)
    pure others.isEmpty

/-- Put the driver, and so every child it starts later, under a cgroup with
`memory.max` at `limit`, when its own cgroup allows it: the cgroup is
writable by the driver's user, has the memory controller, and can enable
it for a child (kernel cgroup-v2, Delegation; `canEnableController`). The
driver moves itself into a new child cgroup, so its own cgroup holds no
process and can give the memory controller to the child. On a host that
does not allow it, the result names the reason, and the run continues
with the admission and the per-probe cap only. -/
def setupTreeLimit (limit : KiB) : IO TreeLimit := do
  let txt ← IO.FS.readFile "/proc/self/cgroup"
  let some line := (txt.splitOn "\n").find? (·.startsWith "0::")
    | return .none "/proc/self/cgroup has no cgroup v2 line"
  let dir : FilePath := "/sys/fs/cgroup" ++ ((line.splitOn "0::").getD 1 "")
  let controllers ← IO.FS.readFile (dir / "cgroup.controllers")
  unless controllerListed controllers "memory" do
    return .none s!"{dir} has no memory controller"
  for f in ["cgroup.procs", "cgroup.subtree_control"] do
    unless ← writable (dir / f) do
      return .none s!"{dir / f} is not writable by this user (no delegation)"
  let pid ← IO.Process.getPID
  unless ← canEnableController dir "memory" pid do
    return .none s!"{dir} has another task, so cgroup v2 refuses to enable memory there (No Internal Process Constraint)"
  let child := dir / s!"lean-mend-{pid}"
  IO.FS.createDir child
  IO.FS.writeFile (child / "cgroup.procs") s!"{pid}\n"
  IO.FS.writeFile (dir / "cgroup.subtree_control") "+memory\n"
  IO.FS.writeFile (child / "memory.max") s!"{limit.val * 1024}\n"
  pure (.cgroup child limit)

end LeanMend.Shell
