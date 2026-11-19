# Static cross-toolchain diff

This document is the design for a lean-mend phase that predicts the findings of
a bump, and their causes, from elaborated terms alone. No repair runs and no
target code executes. Status: design, not built.

## The problem

A bump moves a target from toolchain A (for example Lean v4.29.0 with its
Mathlib) to toolchain B (Lean v4.33.1). Today lean-mend finds an axiom or a
behavior difference only at the end of a run, in `certificate` and `compare`
(`docs/machine.md`). The cause then needs a separate search. EquiVM run 10
(2026-11-07) shows the cost: 43 Violation cards and 2 Behavior cards after a
run of 13 504 s. All three causes were knowable from elaborated terms:

| Edit | Cards | Cause | Where the cause lives |
|---|---|---|---|
| E1 | 38 | Mathlib `List.find?_congr` gained `Classical.choice` (its proof became `induction l with grind`) | a dependency constant |
| E2 | 4 | Lean core `Lean.Loop.forIn` went from no axioms to `[propext, Classical.choice, Quot.sound]` | a dependency constant |
| E3 | 1 | the v4.33.1 match compiler compiles a `match` on `Nat` literals to sparse cases that use `propext` | a generator: auxiliaries in the target's own build |

The release notes do not state these effects. They mention `_sparseCasesOn`
auxiliaries only for a private-name defect (v4.30.0 #12964) and a diagnostic
defect (v4.31.0). So a catalogue built from release notes
(`docs/breaking-changes.md`) cannot predict them. Elaborated terms can.

## Prior art

- **Comparator** (leanprover/comparator; in Lean core as `lake comparator` and
  `lake check` since v4.35.0). On one toolchain, it checks that a solution's
  theorems have the same statements as a challenge's, use only permitted axioms,
  and are accepted by the kernel. It does not compare two toolchains, and it
  does not compare what definitions compute.
- **lean4export** (leanprover/lean4export). It writes an environment's kernel
  declarations as NDJSON, one export per Lean version. It is a building block
  for this design.
- **lean4checker** replays an environment through the kernel, on one toolchain.

No tool found (2026-11-07) compares two toolchains' environments of the same
source for axiom sets, generated auxiliaries and computational equality.

## The mechanism

Each side is elaborated by its own toolchain. The base worktree holds side A's
build, and the target holds side B's. Neither side elaborates the other's
source. Each side exports its terms through the probe, as the certificate does
today.

### 1. The dependency diff

For every constant of the dependencies (Lean core, Std, Batteries, Mathlib and
any other package), at each side: its axiom set, and the source text of its
declaration command with its scope (§ 4, step 3). The diff lists each constant
whose axiom set or source text differs, and each constant that exists at one
side only, with its module and package revision at each side. Axiom sets are
names, the same at both versions, so comparing them is not a comparison of one
toolchain's output with the other's. The proof-erased body hash that this diff
compared before decision S12 is such a comparison, and is replaced by the
source text: an unchanged command whose elaboration differs between the
versions is no entry (T1).

**Scope (slice 2, revised).** Exported over the whole dependency closure
(every constant of Lean core, Std, Batteries and Mathlib), `export` did
not finish on EquiVM's pins: a target's own closure reaches only a small
fraction of what the whole closure holds. The diff is instead scoped to
the constants the target's own declarations use (`export --closure`): the
walk seeds from every constant the target's own modules declare, over
`axEdges`, so the diff still serves every target whose own declarations
use the same dependency constants, but it is no longer independent of
every target, only of targets with the same used-constant closure. The
cache key reflects this: each side's own-module list is part of it
(§ Storage), so a target whose own modules change, with no pin change,
recomputes.

The default covers every built module of the target (`moduleGraph`,
filtered to a built `.olean` — the same set `Shell.Target.certificate`
covers), with no person choosing which ones: a first design let a
caller restrict the scope with `--roots`, and the restriction silently
dropped a real finding (`Lean.Loop.forIn`, E2) on EquiVM's own pins,
because the chosen roots did not reach it. `--roots` is removed.

Two independently-built executable roots that each declare their own
`main` cannot be in the same `importModules` call (a genuine Lean
limit, not one of this tool's making — EquiVM's pins have exactly this
shape, `Tests.DiffTest.Main` against `Examples.ERC20.SpecTests`).
`LeanMend.Shell.DepDiff.exportRows` recovers the way
`Shell.Target.declsOf` already does for the certificate: on the clash
Lean reports, drop the named module from the call and retry
(`clashModule`), run every module dropped this way in its own later
call, seeded from and excluded by the same, full own-module list every
call uses, and take the union of every call's rows, by name. A clash
costs one extra probe call per colliding module, never a missing one.
`tests/dep-diff-clash.sh` checks this directly: two modules that declare
the same top-level name, each using a different dependency constant, and
the diff reaches both.

**Storage (slice 2, `LeanMend.Shell.DepDiff`).** Each side's `export
--closure` call(s) are rooted at every built module of the target
(`moduleGraph`), with the target's own rows dropped from the result (the
walk's own own-module list excludes them from the output, not only its
roots). The key is both toolchains, both `lake-manifest.json`s'
`(package, rev)` pairs, each side's built-module list, and each side's
built content (`builtContentHash`: the path and the bytes of every `.olean`
under `.lake`, law LM3), canonicalized and hashed with `hash`
(`Shell.Target.probeStamp` keys the compiled probe the same way). The file
is `<after>/.lean-mend/dep-diff/<key>.json`, next to the target's other
`.lean-mend` state; `lean-mend dep-diff <base> <after> [--cache <dir>]`
overrides the directory for a caller that shares one store across targets.
A second call with the same pins, the same built-module list and the same
built files reads the file instead of exporting again
(`tests/dep-diff-rebuild.sh`: a rebuild that changes one dependency proof,
with the manifest and module list unchanged, computes a fresh diff). The
content hash reads every built file once per call: on EquiVM's trees, 42.8 s
for probe-base (4 354 `.olean` files) and 55.9 s for mend-target (9 647
files), 2026-11-12, against about 9.5 minutes for the export it saves.

**Cost (measured, EquiVM's pins: probe-base v4.29.0/mathlib 8a178386,
mend-target v4.33.1/mathlib 0df444a3).** The unscoped export did not
finish in either of two attempts (50 and 59 minutes). Three defects, now
fixed, accounted for most of the cost, measured on a Lean-core-only
`Std` export (76 557 constants, no Mathlib): an `IO.Ref` left aliased to
its own old value during `axiomsOf`'s SCC walk forced every
`Std.HashMap.insert` to copy instead of mutate in place (127-168 s wall
before the fix, 14 s after, identical output); `export` called
`erasedBody` on every `theorem`'s own proof term, which proof
irrelevance makes unnecessary; comparing a `def`'s erased body by its
full term, not a hash, forced every unchanged large term's JSON to be
built and compared in full. Closure scoping alone, on a `Std`-importing
target that calls one `Std.HashMap` function: 12.21 s wall for the whole
closure, 1.26 s scoped — a 9.7x reduction, output 78 519 lines against
2 329.

With all four fixes and the default scope (every built module, no
`--roots`): **9:29.53 wall, 5.49 GiB peak resident, 8 202 entries**.
`Lean.Loop.forIn` is an axioms-changed entry, gaining exactly `propext`,
`Classical.choice` and `Quot.sound` — decision S2's E2.
`List.find?_congr` is an onlyAfter entry, `Classical.choice` among its
axioms: it is not a moved lemma in this Mathlib pair, it is a new one
(absent from base's `Mathlib/Data/List/Find.lean` and
`Mathlib/Data/Multiset/Find.lean` entirely; present at after) —
decision S2's E1, under the scoped design, correctly reported as new
rather than axiom-changed.

Run 10: this diff contains `List.find?_congr` (E1) and `Lean.Loop.forIn` (E2).

### 2. Propagation through the target

The target's constant graph at side B (the edges the certificate already reads,
`axEdges`) maps the dependency diff to the target declarations that reach a
changed constant. For each one: the predicted axiom change, and the path to the
changed constant (the same form as a Violation card's cause,
`docs/verification.md` § What a card explains).

**Not built yet.** A target declaration whose after-side path reaches an
`onlyAfter` dependency entry (§ 1: a dependency constant new to the
after pin, not a moved one — `List.find?_congr` on EquiVM's pins) is a
cause too, the same as an axioms-changed entry: the new constant's own
axioms are what it adds to the path. § 2's mapping must read an
`onlyAfter` entry's `after` row the same way it reads an `axioms`
entry's, not only the `axioms`/`body` cases.

Run 10: this gives the 38 E1 cards and the 4 E2 cards, with their causes,
before any repair.

### 3. Generated auxiliaries of the target

Some changes live in a generator, not in a constant: the match compiler, the
equation compiler, `deriving` handlers, structural or well-founded recursion.
Their output is a set of auxiliary constants in the target's own build. For
each target declaration, compare its auxiliaries at the two sides (their axiom
sets and erased bodies), matched by owner and role, not by name, because the
names can differ between versions.

**Built (slice 4).** `LeanMend.Core.GenAux`/`LeanMend.Shell.GenAux`, CLI
`lean-mend gen-aux <base> <after>`. A new probe arm, `export --ownClosure`
(`cmdExportOwnFull`), gives each side's own-module constants (the complement
of `--closure`'s filter, no closure walk — a direct module-membership filter,
since a generated auxiliary is declared in the same module as its owner).
Owner and role are read from the auxiliary's own name: `ownerNames`/
`generatedPart` (`LeanMend.Core.Cause`, reused unchanged) find the owner from
a `_`/`match_`-prefixed component; one more generated shape, a `deriving`
handler's own output (a bare `default` suffix), is added for this slice.

The comparison is **reachability-bounded**, not a blanket per-module grouping:
for each target declaration, walk its own `uses` edges, continuing only
through a generated auxiliary (stopping at the first other real declaration —
the owner-rule's own boundary, `docs/machine.md` § The site of an axiom
finding), and group only what that walk reaches. An unbounded, name-shape-only
grouping (an earlier draft) is wrong two ways, both measured on EquiVM's pins:
a `match_N` Lean keeps only to state an equation lemma for `simp`, never
called by the declaration's own compiled value, still carries a stale axiom
and would be unioned in regardless (`allocationSizes.match_7` at v4.29.0, axioms
already `[propext]`, unreached); and an unbounded walk through a real
declaration's own callers lets an unrelated proof elsewhere that unfolds the
declaration via `simp` absorb that caller's whole further closure, which
reproduced the same false negative from the other direction. A third bug
found the same way: Lean's own equation lemma (`f.eq_1`, …, `f.eq_def`,
no `_`/`match_` prefix, `Lean.Meta.Eqns`) is not caught by `generatedPart`'s
`_`/`match_`-only test, so it was wrongly treated as an independent real
declaration; its own proof term cites the matcher it unfolds, so its own
walk rediscovered `f`'s matcher at a side where `f` itself never reaches
it. Fixed by recognizing the `eq_N`/`eq_def` shape as generated too
(`auxOwnerRole`). A fourth: Lean can name a `where`-bound helper's own
inner match flatly under the PARENT's numbering (`allocationSizes.match_1`,
not `allocationSizes.refExprs.match_1`) at one toolchain. So the walk keys a
found auxiliary by the root that found it. A fifth: the walk took every
generated name it reached as the root's own, so a theorem whose proof uses
another declaration's `eq_1` got that lemma's axioms as its own auxiliary.
On EquiVM's pins this gave 228 false predictions (227 equation lemmas, 1
matcher). An auxiliary is now the root's only when its name-parsed owner is
the root or a namespace ancestor of the root; any other generated name is a
boundary (`tests/GenAuxTest.lean`, "another declaration's equation lemma").

Run 10 has no finding of this class. Its E3 finding
(`Stele.Interp.allocationSizes`, `propext` at the after side) comes from a
source edit, not from the toolchain. At the base commit (EquiVM `1ac3d7b5`)
the declaration is a `partial def`: opaque, with no axioms and no reachable
auxiliary. EquiVM commit `7a115578` ("lean-mend run 9 repairs plus 8 hand
edits") rewrote it as total structural mutual recursion, whose matcher's
sparse `casesOn` uses `propext`. Measured 2026-11-11 with `#print axioms`
and the constant's own `uses` in each tree. This explains why no Lean-core
fixture reproduced a toolchain-only difference (six attempts here, more in
the Level 3 work). The E3 card's cause is the declaration's own source change,
which § 4 and the Behavior path cover.

On EquiVM's pins, after the fifth fix, `lean-mend gen-aux` reports 96 diff
entries and 0 predictions, in 849.6 s with 4.62 GiB peak resident size
(2026-11-11, no other probe run at the same time). That equals run 10's count
of generator-caused findings, 0.

### 4. Computational equality of a changed definition: transport and prove

A changed `def`, `instance` or `abbrev` gives a Behavior finding. This step
certifies that the new definition computes what the old one computed. It never
compares the output of one toolchain with the output of the other (decision
S12).

**Why not compare across toolchains.** A first design (2026-11-11 to
2026-11-15) compared the two sides' erased terms structurally. Every change in
how a toolchain elaborates or compiles the same source made a spurious
difference, and each needed its own patch: the recursion encoding of
`List.replicate`, bound universe names (`u` against `u_1`), the instance path
of `2 ^ k` (`instPowNat` against Mathlib's `NPow.toPow`), the loop-state tuple
of `do` notation (`Prod` against `MProd`). Comparing compiled code does not
escape this: v4.33.1 moved the IR passes `ExpandResetReuse`, `PushProj`,
`SimpCase` and `SimpleGroundExpr` into LCNF and changed `Lean/Compiler/LCNF`
by 2 211 lines (read from the two toolchains' sources), so an unchanged program
compiles to a different IR. The cause is the comparison itself: one toolchain's
output against another's.

**The method.** Every equality is decided inside the new toolchain, by its own
kernel. The old toolchain contributes only its kernel terms, which are the
exact meaning of the old program.

1. **Transport.** The probe at the old toolchain emits the old declaration's
   kernel term (its type and value, with universe parameters, every constant by
   name). The probe at the new toolchain rebuilds that term in the new
   environment and adds it as `LeanMendOld.<decl>`, outside the target (D10).
   The new kernel checks it. Each constant the old term names is resolved by
   name in the new environment.
2. **Prove.** At the new toolchain, a list of tactics tries
   `@LeanMendOld.<decl> = @<decl>`: `rfl` first (the kernel's definitional
   equality, which already identifies instance paths that Mathlib keeps
   defeq, every universe renaming, and every elaboration that unfolds to the
   same term), then the lemma that the edit's own rule ships (below), then the
   general lemmas of the prelude (`probe/ProvePrelude.lean`). Lean checks the
   proof. A failed proof certifies nothing.

   **A kernel value that is not what runs proves nothing.** The kernel value
   of a `partial def` is a placeholder (`mkInhabitantFor`, kind `opaque`;
   the real recursion is the separate `_unsafe_rec` constant, which the
   kernel cannot reason about: `Lean/Elab/PreDefinition/Main.lean:20-33`,
   `Basic.lean:280-294`). The same holds for `opaque`, `implemented_by` and
   `extern`. Two placeholders can be `rfl`-equal while the programs differ.
   So a constant of these kinds, at either side, is never certified by step 2:
   step 3 decides it by its source text alone, under T1, or it is a trust
   point (S4).

   **Algorithm changes need their own lemma.** Equality of two algorithms is
   undecidable, so no fixed tactic list covers every new one. A lean-mend rule
   whose edit changes an algorithm (not only a proof or a name) ships the
   lemma that proves its edit preserves the result, as `whileChunk_bodies`
   does for the `while` to `for` rule: every edit that lean-mend makes is then
   proved by construction, and a rule without such a lemma is not a rule
   lean-mend applies on its own. An algorithm change that lean-mend did not
   make (a person's edit in the bump, or a dependency's) and that no shipped
   lemma proves gets a card, or, for a dependency, a trust point. S6 and § 6
   hold: the card states each attempt.
3. **Name the cross-version assumptions.** The transported term means at the
   new toolchain what it meant at the old toolchain if every constant it names
   (and, recursively, every constant those name) means the same at both. For
   each such constant, in order:
   1. A kernel value that is what runs (not the kinds of step 2's rule):
      transport its old term and try `rfl` against its new definition in the
      new kernel. Equal: the walk continues into what it names.
   2. Else, compare its **source text**, never elaborated terms: the text of
      its declaration command (`findDeclarationRanges?`, read from the
      toolchain's `src/lean`, the package checkout, or the target), together
      with the text of the commands that scope it (`namespace`, `section`,
      `variable`, `open`, `set_option` before it in its file). § 1 already
      stores this verdict for every constant of the target's used-constant
      closure, per pair of pins (§ 1 Storage); the walk reads it there, and
      computes it only for a constant outside that closure.
      - The same text at both pins: the same meaning under T1 (below). The
        constant is listed on the certificate as accepted under T1, and the
        walk continues into what it names.
      - A different text: a real change. Step 2's tactics are tried on the
        constant itself; if none proves it, it is a **trust point** of the
        certificate, listed by name with the reason (S4).
   3. A constant that cannot be transported (absent at the new toolchain, a
      different type, a private name that no longer exists) goes straight to
      2.

   A generated constant (a matcher, an equation lemma, a structure projection,
   `deriving` output) has no declaration range of its own; its owner's command
   text stands for it (`ownerNames`). A theorem is not walked: proof
   irrelevance (D16) makes only its statement matter, and the transported term
   type-checks against it.

**T1, the one global trust point.** The same source text means the same program
at both Lean versions and dependency pins. It covers elaborator rewrites (the
`do` notation of v4.32), compiler changes, and also library drift that leaves a
declaration's own text unchanged but changes how it elaborates: a new or
reprioritized instance in an imported module, notation moved elsewhere. T1 is
applied only where the new kernel cannot decide (step 3.1 failed), and each
constant accepted under it is listed by name on the certificate, so no use of
T1 is silent. People accept T1 once, as policy.

**Instance resolution is a reference too.** The same text `2 ^ k` can resolve to
a different instance at the new pin. The transported old term names the old
instance (`instPowNat`), so step 2 proves the old resolution equal to the new
one in the new kernel (`rfl` when the instances are defeq). A non-defeq
instance change fails the proof: a real difference, never a false certificate.

**Proofs inside the old term** (array bounds, termination arguments) are
transported with it. A proof that names a lemma absent at the new toolchain
makes transport fail at that constant; step 3's rule then applies to that
lemma's statement, never to its proof.

A definition whose proof fails gets a Behavior card that states each attempt:
the transport (and any constant that could not be transported), each tactic
tried, and the first changed constant on the source walk.

### 5. A changed algorithm

A change that computes the same values by a different algorithm (run 10's E2,
`Rng.bigNat` from `while` to `for`) is the same method: transport the old term,
prove it equal at the new toolchain. Only the tactic differs: `rfl` fails, and
the lemma that the `while` to `for` rule ships closes it (`whileChunk_bodies`:
a `while` loop whose step lowers a counter by `min rem c` equals a `for` loop
over `List.replicate ((n + (c − 1)) / c) ()`, proved 2026-11-13 by strong
induction on the counter with `Lean.Loop.forIn_eq_of_monadTail` for one step).

The old term names `Lean.Loop.forIn`. At v4.29.0 it is a `partial def`: its
kernel value is a placeholder, so step 2's rule sends it to step 3.2. Its source
changed (`repeatM` at v4.33.1), so it is a trust point: the compiled run-time
meaning of `while` did not change between the two versions. With T1, that is the
whole certificate. This is the trust point the first design of this section
predicted.

### 6. No finding reaches a person without a certification attempt

The goal of lean-mend is a fully correct bump with no human feedback per
finding. So before a Violation or Behavior card is issued, lean-mend records an
attempt to certify or to repair the finding: § 4, § 5, and the axiom-repair
phase (`docs/machine.md` § Level 3). A card is issued only when each attempt
failed, and the card states why each one failed. People set policy once (which
trust points are accepted); they do not judge findings one by one.

The limit, stated: every edit that lean-mend makes is certified by
construction (each rule ships its proof, S7). A finding still reaches a person
when the bump itself (not lean-mend) changed an algorithm, in the target or in
a dependency, and no shipped lemma proves the change. Program equality is
undecidable, so no method removes that case; a lemma written for it once
certifies every later finding of the same shape.

## Decisions

- **S1.** Each side is elaborated by its own toolchain. lean-mend never
  elaborates one side's source at the other side's toolchain.
- **S2.** The dependency diff is scoped to the constants a target's own
  declarations use (§ 1's revised scope), computed once per pair of pins
  and own-module list, so a target with the same used-constant closure
  reuses the stored diff — revised from "independent of the target": the
  unscoped diff did not finish on EquiVM's pins (§ 1, measured).
- **S3.** A Behavior card is issued only when § 4 cannot certify equality, and
  then it states each attempt and the first changed constant on the source walk.
- **S4.** A constant whose kernel value is not what runs (`partial`, `opaque`,
  `implemented_by`, `extern`) is never certified by a kernel proof (two
  placeholders can be `rfl`-equal while the programs differ). It is equal
  under T1 when its source text is unchanged, and otherwise a stated trust
  point. A trust point is never silently treated as equal: it is listed on
  every certificate that relies on it.
- **S5.** The phase runs before the repair phase. Its predictions are checked
  by the existing `certificate` and `compare` at the end of the run. A
  difference between a prediction and the final certificate is itself a
  finding.
- **S6.** A finding becomes a card only after a recorded, failed attempt to
  certify or repair it (§ 6). The card names each attempt and its reason.
- **S7.** A changed algorithm is certified by a proof at the new toolchain plus
  the stated trust points of its source walk (§ 5), never by sampled inputs. A
  lean-mend rule that changes an algorithm ships the lemma that proves its
  edit; an algorithm change that lean-mend did not make and that no shipped
  lemma proves gets a card or a trust point.
- **S8.** Superseded by S12. It compared equation lemmas across toolchains, a
  patch to the cross-toolchain comparison that S12 removes (the code is on the
  unmerged branch `prove-eq`; its patches for universe names, axiom-only
  changes, instance paths and opaque dependencies are superseded as well).
- **S12.** lean-mend never compares one toolchain's output with the other's:
  not elaborated terms, not erased terms, not LCNF or IR. Each equality is
  proved inside the new toolchain, between the old declaration's transported
  kernel term and the new declaration (§ 4). Across toolchains it compares only
  source text, and the one global trust point T1 (the same source text means
  the same program at both versions) is accepted once as policy and listed on
  every certificate. S1 holds: no source is elaborated at the other side's
  toolchain; the old side contributes kernel terms only.

## Slices

1. The probe exports, per constant: axiom set, used constants, and the
   proof-erased body, at each side. Acceptance: on a fixture pair (Lean v4.29.0
   and v4.33.1, a dependency v1 and v2), the export lists a lemma that gains
   `Classical.choice` and a lemma that moves to another module.
2. The dependency diff (§ 1), stored per pair of pins. Acceptance: on the
   EquiVM pins (mathlib 8a178386 against 0df444a3), the diff contains
   `List.find?_congr` and `Lean.Loop.forIn`.
3. Propagation (§ 2). Acceptance: on run 10's builds, the predicted findings
   are the 42 E1 and E2 cards, with their causes.
4. Generated auxiliaries (§ 3). Acceptance: on run 10's builds, no prediction
   (run 10 has no generator-caused finding; E3 is a source edit, § 3); the
   Core cases in `tests/GenAuxTest.lean`.
5. Computational equality (§ 4), revised by S12. Acceptance:
   - run 10's two Behavior findings (changes in proofs only) certify equal by
     transport and `rfl`, with T1 as the only trust point;
   - a fixture where the same `2 ^ k` resolves to different but defeq
     instances at the two pins certifies by `rfl`;
   - a fixture where a dependency definition's source changes so that it
     computes something else gives a card naming that constant;
   - a fixture whose old term names a constant absent at the new toolchain
     lists that constant as a trust point, or names it on the card.
6. A changed algorithm (§ 5). Acceptance: a fixture where a `while` loop becomes
   a `for` loop between v4.29.0 and v4.33.1 is certified with
   `Lean.Loop.forIn` as its one trust point beyond T1; the same fixture with a
   wrong loop bound is not certified; on run 10's builds, `Rng.bigNat` after E2
   is certified the same way.
7. Integration with the run (S5, S6). Acceptance: a fixture run whose
   predictions equal its final findings; a fixture where they differ gives a
   finding; a card for a finding states each failed certification attempt and
   its reason.

## Cost

Measured for the scoped dependency diff (§ 1 Scope, S2): it reads the target's
own used-constant closure at each side, once per pair of pins, built-module list
and built content; on EquiVM's pins 9:29 wall and 5.49 GiB, 8 202 entries, plus
the content hash (§ 1 Storage). § 4 reads its source verdicts from that stored
diff, so § 4 itself costs the transport, the proof and the walk outside the
closure, per changed declaration. The run 10 card evidence, which reads only the
closures of the findings, took 370.5 s and 2.7 MB at both sides
(`docs/verification.md` § What a card explains).

Slice 5, measured on EquiVM's pins (mend-cache/probe-base v4.29.0,
mend-target v4.33.1, a shared, loaded host, before decision S8): one
`comp-eq` call against both Behavior findings' declarations together, one
`terms` call per side, 4:51.52 wall, 4.59 GiB peak resident (`/usr/bin/time
-v`). A second, independent run measured 268.57 s wall. Neither certified
equal before decision S8 (§ 4, "A spurious difference...").

The same call, after decision S8, with a `strings`-confirmed non-stale
probe (`strings <binary> | grep <a doc string just added to
probe/Probe.lean>`): 5:21.68 wall, 4.25 GiB peak resident; both findings
certify equal, with no trust point. `Rng.bigNat` after the E2 edit, same
pins, the after side an untracked scratch worktree with the one-file edit
and an incremental `lake build` (17.9 s, reusing the untracked copy's
existing `.lake/build`): 6:24.31 wall, 4.25 GiB peak resident; not equal,
first differing subterm named.

Slice 4 (`gen-aux`, EquiVM's pins, `mend-cache/probe-base` against
`mend-target`, one `export --ownClosure` call per side over every built
module, no `--roots` choice): 10:15.5 wall, 4.84 GiB peak resident, bounded by
the target's own size (no dependency constant is ever emitted by this arm).
