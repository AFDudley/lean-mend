/-!
# The memory limit of a run

The pure part of the memory limit of a lean-mend run (`docs/parallel.md`
P17, decision P24, slice S5). The design follows Bazel's local resources: each
running work item is charged its estimated peak, and new work starts only
when the charges fit the limit.

* The limit: `--max-memory <GiB>`, or else `MemAvailable` at run start minus
  a reserve (`MemoryLimit.limit`).
* The charge of one work item (a module probe, a nested speculative probe, a
  module build): `workEstimate`, the largest peak of one probe of EquiVM run
  7, rounded up.
* Admission (`admits`): the driver's measured size plus the charges of the
  running work plus the charge of the new work fit the limit, and the
  measured process tree plus what each live probe can still grow into plus
  the new charge fits the limit. When nothing runs, one item starts even if
  it does not fit, so the run progresses (Bazel's
  `--allow_one_action_on_resource_unavailable`).
* The hard cap of one probe: `probeCap`, the charge times a margin. The probe
  runs under `lean -M`, so Lean stops it when its resident size passes the
  cap.

A speculative round of width `w` uses the probe that its module already
holds, and at most `w - 1` other probes that `admits` gives it with no wait
(`roundPlacement`). A candidate with no probe of its own runs on the module's
probe, in rule order. So a round never waits for memory while it holds a
probe.
-/

namespace LeanMend

/-- A memory size in kibibytes, the unit of `/proc`. -/
structure KiB where
  val : Nat
  deriving DecidableEq, Repr, Inhabited

/-- `n` gibibytes. -/
def KiB.ofGiB (n : Nat) : KiB := ⟨n * 1024 * 1024⟩

/-- The memory that the default limit keeps free of the run: the file pages
that the tree maps (the `.olean` files; one probe maps up to 1.8 GiB), the
kernel, and the growth of other processes. `docs/parallel.md` P24 gives the
source. -/
def reserveDefault : KiB := KiB.ofGiB 16

/-- The charge of one work item, its estimated peak. The largest peak
resident size (`VmHWM`) of a probe `lean` process of EquiVM run 7 was
10302488 KiB (9.83 GiB, `Examples.ERC20.TransferFrom`). The peaks did not
grow with the module's size in bytes or declarations, so the estimate is one
constant. `docs/parallel.md` P24 gives the data. -/
def workEstimate : KiB := KiB.ofGiB 10

/-- The margin of the hard cap over the charge: 3/2. The largest probe peak
of run 7 was 1.56 times the mean peak (9.83 GiB against 6.30 GiB), and a
probe of a module that still mends can grow past the largest peak seen. -/
def capMargin : Nat × Nat := (3, 2)

/-- The hard cap of one probe: the charge times the margin, 15 GiB. -/
def probeCap : KiB := ⟨workEstimate.val * capMargin.1 / capMargin.2⟩

/-- `k` in mebibytes, rounded down, for `lean -M`. -/
def KiB.toMiB (k : KiB) : Nat := k.val / 1024

/-- Where the run's limit comes from. -/
inductive MemoryLimit where
  /-- `--max-memory <GiB>`. -/
  | flag (limit : KiB)
  /-- No flag: `MemAvailable` at run start, minus `reserve`. -/
  | available (memAvailable : KiB) (reserve : KiB := reserveDefault)

/-- The limit of the run. -/
def MemoryLimit.limit : MemoryLimit → KiB
  | .flag l => l
  | .available a r => ⟨a.val - r.val⟩

/-- The state of the run at one admission. -/
structure Load where
  /-- The measured private resident memory (`RssAnon` plus `RssShmem`) of
  the driver process alone: the plans and the machine state. -/
  driver : KiB
  /-- The measured private resident memory of the driver and every process
  below it. -/
  tree : KiB
  /-- Each live probe: the measured private memory of its process tree, or
  `none` before its process starts. -/
  probes : List (Option KiB)
  /-- The other running work of the schedule: the `lake build +<module>`
  tasks. -/
  others : Nat := 0

/-- The charged total if one more item starts: the driver's measured size,
the charge of each running item, and the charge of the new item. -/
def Load.charged (l : Load) (est : KiB) : KiB :=
  ⟨l.driver.val + est.val * (l.probes.length + l.others + 1)⟩

/-- The measured total if one more item starts: the measured tree, plus the
part of the charge that each live probe can still grow into, plus the charge
of the new item. A probe that has not started counts with its whole
charge. -/
def Load.measured (l : Load) (est : KiB) : KiB :=
  ⟨l.tree.val + (l.probes.map fun p => est.val - (p.map (·.val)).getD 0).sum + est.val⟩

/-- Nothing of the schedule runs: no probe and no other work. -/
def Load.idle (l : Load) : Bool := l.probes.isEmpty && l.others == 0

/-- One more item may start: both totals stay within the limit, or nothing
runs. The second case lets the run progress when one item alone does not fit:
no running work can end and free memory, so a wait would never end. -/
def admits (limit est : KiB) (l : Load) : Bool :=
  (decide ((l.charged est).val ≤ limit.val) && decide ((l.measured est).val ≤ limit.val)) || l.idle

/-- When nothing runs, one item always starts, so the run progresses. -/
theorem admits_idle (limit est driver tree : KiB) : admits limit est ⟨driver, tree, [], 0⟩ = true := by
  simp [admits, Load.idle]

/-- When something runs, an item starts only when its charge fits: the
charges of the live probes, the running builds and the new item, with the
driver, stay within the limit. So at most `limit / est - 1` probes are live
before an admission. -/
theorem admits_within (limit est : KiB) (l : Load) (h : l.idle = false)
    (ha : admits limit est l = true) :
    l.driver.val + est.val * (l.probes.length + l.others + 1) ≤ limit.val := by
  simp [admits, h, Load.charged] at ha; exact of_decide_eq_true ha.1

/-- The `decls-batch` probe processes that a run's certificate starts at once
(`Shell.Target.certificate`): 4, as before the limit, at most as many charges
as the limit holds, and at least 1. The certificates run before and after the
dataflow schedule, when no module probe lives. -/
def certificateJobs (limit est : KiB) : Nat := max 1 (min 4 (limit.val / est.val))

/-- The stop of a run when a probe passes its hard cap: Lean stopped the
probe with "excessive memory consumption detected" (`lean -M`). `peak` is the
probe's own peak resident size (`VmHWM`) at its last reply. -/
structure CapExceeded where
  module : String
  cap : KiB
  peak : KiB
  deriving Repr

def CapExceeded.message (e : CapExceeded) : String :=
  s!"lean-mend: the probe of {e.module} passed its memory cap of {e.cap.val} KiB \
    (lean -M {e.cap.toMiB}); its peak resident size at its last reply was {e.peak.val} KiB"

/-- The probe that one candidate of a speculative round runs on. -/
inductive Placement where
  /-- The module's own probe, in the module's own worktree. -/
  | own
  /-- A probe of its own, in a nested worktree. -/
  | nested
  deriving DecidableEq, Repr

/-- The probes a speculative round asks for in addition to its module's own
probe: one for each candidate after the first. -/
def roundExtra (width : Nat) : Nat := width - 1

/-- The placement of the `width` candidates of a round, in rule order, when
the round got `extra` probes with no wait. The first candidate runs on the
module's own probe. The next candidates run on their own probes, at most
`extra` of them. The remainder runs on the module's own probe, one at a time,
after the first. -/
def roundPlacement (width extra : Nat) : List Placement :=
  if width = 0 then [] else
    .own :: (List.replicate (min (width - 1) extra) .nested ++
      List.replicate (width - 1 - min (width - 1) extra) .own)

/-- A round runs `min (width - 1) extra` nested probes: never more than it
got, and never more than its candidates after the first. -/
theorem roundPlacement_nested (width extra : Nat) :
    (roundPlacement width extra).count .nested = min (width - 1) extra := by
  unfold roundPlacement
  split
  · simp_all
  · simp [List.count_append, List.count_replicate]

/-- A round places each of its `width` candidates. -/
theorem roundPlacement_length (width extra : Nat) :
    (roundPlacement width extra).length = width := by
  unfold roundPlacement
  split
  · simp_all
  · simp; omega

/-- The pid of every process below `root`, and `root` itself, from each
process's parent (`/proc/<pid>/stat`). Each step of the walk adds one
generation; a process tree has at most as many generations as processes. -/
def processTree (parents : List (Nat × Nat)) (root : Nat) : List Nat :=
  go parents.length [root] [root]
where
  go : Nat → List Nat → List Nat → List Nat
    | 0, acc, _ => acc
    | n + 1, acc, gen =>
      let next := (parents.filter fun (p, pp) => gen.contains pp && !acc.contains p).map (·.1)
      if next.isEmpty then acc else go n (acc ++ next) next

end LeanMend
