# Breaking changes in Lean 4.30–4.35, and learnings from related tools

This catalogue is the input for lean-mend rules that answer a Lean release's
breaking changes before a run meets them (`docs/rules.md`). A subagent
compiled it from the release notes and from hopscotch, downstream-reports
and AXLE, on 2026-10-26. The operator checked the claims in § Corrections
against the EVMLean diff and the run-21 ledger. § Decisions states what
lean-mend builds from it.


Scope note: this file does not edit any tracked file. It reports research only.
Every claim about an external project cites its primary source. Unverified
claims carry an `[UNVERIFIED]` or `[INFERENCE]` tag.

Sources read for Part 1: the Lean release notes at
`https://lean-lang.org/doc/reference/latest/releases/v4.30.0` through
`v4.35.0` (each release's own "Breaking Changes" section and, where a symptom
needed it, the full Language/Library section). Sources read for lean-mend
itself: `docs/rules.md`, `docs/machine.md`, `LeanMend/Spec/Types.lean`,
`LeanMend/Core/Classify.lean`, and the 11 files in `rules/proposed/`.

## Part 1: Lean release breaking changes

### How to read the table

- **Symptom** is the error text or `kind` lean-mend's `classify`
  (`LeanMend/Core/Classify.lean`) would see, where a match exists; otherwise
  `unknown` (no rule can target it today, by construction).
- **Coverage** names an existing file in `rules/proposed/`, or `none`.
- A `none` row gives either a rule in lean-mend's JSON shape built from
  **existing** `EditOp`s, or a one-sentence spec for the new operation it
  needs. No proposal adds a declaration (decision D10) or edits a statement
  (decision D5), per `docs/rules.md`.

### Table 1 — v4.30.0 through v4.33.1 (the EVMLean bump range)

| # | Version / PR | Change | Symptom | Mechanical fix | lean-mend coverage |
|---|---|---|---|---|---|
| A | v4.30.0 [#12603](https://github.com/leanprover/lean4/pull/12603) | An `inductive` constructor may now override a parameter's binder kind, but only for parameters in the declaration header; a constructor binder that merely repeats a section `variable` name without a type is read as an (illegal) override. | `Only parameters appearing in the declaration header may have their binders kinds be overridden.` (class `binderOverride`) | Add an explicit type to the binder: `(x)` → `(x : _)`. | `none` |
| B | v4.30.0 [#12897](https://github.com/leanprover/lean4/pull/12897) | `inferInstanceAs A` can no longer substitute for `(inferInstance : A)`; it now requires the source and target types to match exactly. | elaboration failure / `typeMismatch` at the call | Rewrite `inferInstanceAs A` to `(inferInstance : A)`. | `none` |
| C/K | v4.31.0 highlight "Transparency and Defeq Discipline" ([#13492](https://github.com/leanprover/lean4/pull/13492), [#13363](https://github.com/leanprover/lean4/pull/13363), [#13281](https://github.com/leanprover/lean4/pull/13281), [#13512](https://github.com/leanprover/lean4/pull/13512), [#13636](https://github.com/leanprover/lean4/pull/13636), [#13833](https://github.com/leanprover/lean4/pull/13833)), default-flipped by v4.33.0 [#13895](https://github.com/leanprover/lean4/pull/13895) | `simp`/`dsimp` run at `.reducible` transparency; a `def` not marked `@[reducible]`/`@[implicit_reducible]` stops unfolding there, and `isDefEq` now compares a metavariable's type at a stricter transparency before assigning it. | `` `simp` made no progress `` (class `simpNoProgress`), or `Type mismatch: After simplification` where the two printed types look identical (a hidden instance, e.g. `Decidable`, differs) (class `typeMismatch`) | Mark the constant `@[implicit_reducible]`; add the missing projection lemmas to the `simp`/`dsimp` call; or split `simpa [L] using h` into `simp [L] at h ⊢; exact h` (the looser `exact` accepts what `simpa` rejects). | `simpa-hidden-mismatch` (op `simpaSplit`) and `evmlean-subtractGas-unfold` (op `simpArgAdd`) answer **common instances**; the EVMLean run-21 residue shows this family is not fully closed (see "EVMLean evidence" below). |
| D | v4.31.0 [#13807](https://github.com/leanprover/lean4/pull/13807) and [#13528](https://github.com/leanprover/lean4/pull/13528) | The application elaborator now beta-reduces substituted arguments, matching `inferType`/`instantiateMVars`; many `dsimp only` steps that existed only to perform that reduction now do nothing. | `` `dsimp` made no progress `` (class `simpNoProgress`) | Delete the dead `dsimp only` step. | `none`. `docs/rules.md` already documents `deleteTactic` for class `simpNoProgress`, but no rule file uses it. |
| E | v4.31.0 [#13243](https://github.com/leanprover/lean4/pull/13243) | Structure-instance default values no longer apply inside **patterns** (e.g. `s matches { x := 1 }`). | `field missing` (class `unknown`: no text pattern in `classify` matches it) | Supply the missing fields explicitly, or add `..`. | `none`, and no safe generic fix exists: the right fields depend on the pattern's intent, which lean-mend cannot infer. |
| F | v4.31.0 [#13476](https://github.com/leanprover/lean4/pull/13476) | `apply`/`rewrite` now filter assigned metavariables before computing subgoal tags; a lone remaining goal inherits the input goal's tag instead of a fresh one. | a later `case h => …` fails because the tag `h` no longer exists | Rename the `case` tag to match. | `none`; needs a tag-aware operation (one sentence below). |
| G | v4.31.0 [#13627](https://github.com/leanprover/lean4/pull/13627) | `UInt8.ofNatTruncate` renamed to `UInt8.ofNatClamp` (and the other `UIntX` widths). | `unknown identifier` (class `unknownIdentifier`) *if* no `@[deprecated]` alias was kept `[UNVERIFIED]` | Rename the identifier. | Automatic via the **derived** alias-map mechanism (`docs/rules.md` §Entrenchment and order, item 1) if an alias exists; otherwise `none`, though the existing generic `rename` op still answers it once attributed. |
| H | v4.32.0 [#13305](https://github.com/leanprover/lean4/pull/13305) (+[#13912](https://github.com/leanprover/lean4/pull/13912), [#13931](https://github.com/leanprover/lean4/pull/13931)) | The new `do` elaborator becomes the default: `do` now requires a `Pure` instance (not just `Bind`), `do match` arms become non-dependent, `return` inside `(← do …)` now returns from the **enclosing** block. | `failed to synthesize Pure …` (class `unknown`: `classify` only recognizes the text `Decidable` for `missingDecidable`), or a `typeMismatch` in a `do match` arm | Scope `set_option backward.do.legacy true in` before the declaration. | `none` |
| I | v4.32.0 [#13798](https://github.com/leanprover/lean4/pull/13798) | `Std.Time.DateTime (tz : TimeZone)` removed; the former `ZonedDateTime` is renamed to `DateTime`. | `unknown identifier ZonedDateTime` (class `unknownIdentifier`), or a `typeMismatch` where an explicit-tz constructor was used | Rename `ZonedDateTime` → `DateTime`; the explicit-tz constructor case needs a manual argument drop. | The plain-rename case is answerable with the existing generic `rename` op; the argument-drop case is `none`. |
| J | v4.32.0 [#13908](https://github.com/leanprover/lean4/pull/13908) | `Lean.RBMap`/`Lean.RBTree` deprecated in favour of `Std.TreeMap`/`Std.TreeSet`, via a `deprecated_module` shim. | deprecation warning now; `unknown identifier`/`unknown namespace` once the shim is deleted | `renamePrefix Lean.RBMap → Std.TreeMap`, `renamePrefix Lean.RBTree → Std.TreeSet`. | `none`. This is a **different** namespace from `batteries-rbtree-move` (which targets `Batteries.RBMap` only); no rule file answers `Lean.RBMap`/`Lean.RBTree`. |
| L | v4.33.0 [#13956](https://github.com/leanprover/lean4/pull/13956) | Kernel type-checking is now bounded by `maxRecDepth` instead of the native stack, so `(kernel) deep recursion detected` becomes deterministic (and can newly trigger where it did not before). | `(kernel) deep recursion detected` (class `unknown`: no text pattern matches it) | `set_option maxRecDepth <n> in` before the declaration. | `none`; needs a new operation (one sentence below). |
| X | Batteries [PR #1792](https://github.com/leanprover-community/batteries/commit/896aa6735ed650c25e78c905159611a644283e80), "chore: deprecate `Batteries.RBMap` declarations" (merged 2026-05-31) | `Batteries.RBMap`, `RBSet`, `RBNode` moved to the `RBTree.*` namespace, behind a `deprecated_module` with no per-name `@[deprecated]` aliases. | `unknown identifier`/`unknown namespace` (class `unknownIdentifier`) | `renamePrefix Batteries.RBMap → RBTree.RBMap`, etc. | `batteries-rbtree-move` (existing rule; file-wide `renamePrefix`, since a per-site rename fails — see `docs/rules.md` §Edit operations, `renamePrefix` row). |

**Changes read but excluded** (compiler/metaprogramming internals or Lean-tooling-only, no ordinary proof-source symptom): v4.30.0 [#13005](https://github.com/leanprover/lean4/pull/13005) (`compileDecl`/`markMeta`), [#12749](https://github.com/leanprover/lean4/pull/12749) (metaprogramming API renames), [#12771](https://github.com/leanprover/lean4/pull/12771) (`String.Slice.Pos.cast`), [#12435](https://github.com/leanprover/lean4/pull/12435) (`Option.getElem?_inj`), [#12708](https://github.com/leanprover/lean4/pull/12708) (`PostCond.*` implicit order); v4.31.0 [#13030](https://github.com/leanprover/lean4/pull/13030) (level-mvar pretty printing), [#13516](https://github.com/leanprover/lean4/pull/13516) (`Lake.Util.Opaque` namespace); v4.32.0 [#13893](https://github.com/leanprover/lean4/pull/13893) (`lake lint` CLI flags), the nested-action `return` semantics of [#13912](https://github.com/leanprover/lean4/pull/13912) (silent behaviour change, not a build error); v4.33.0 [#14241](https://github.com/leanprover/lean4/pull/14241) (`bv_decide` structure ext), [#14091](https://github.com/leanprover/lean4/pull/14091) (`Float.lt`/`le` Prop→Bool), [#14290](https://github.com/leanprover/lean4/pull/14290) (`int_toBitVec` simp-set split), [#14206](https://github.com/leanprover/lean4/pull/14206) (Lake docstring-lint move), [#14255](https://github.com/leanprover/lean4/pull/14255) and siblings (namespace hygiene moves), [#14372](https://github.com/leanprover/lean4/pull/14372) and [#13679](https://github.com/leanprover/lean4/pull/13679) (C FFI only). v4.32.1, v4.32.2, and v4.33.1 are kernel/runtime soundness patches with no proof-source symptom at all (see their release notes, [v4.32.1](https://lean-lang.org/doc/reference/latest/releases/v4.32.1), [v4.32.2](https://lean-lang.org/doc/reference/latest/releases/v4.32.2), [v4.33.1](https://lean-lang.org/doc/reference/latest/releases/v4.33.1)).

### Table 2 — v4.34.0 through v4.35.0 (the next bumps)

| # | Version / PR | Change | Symptom | Mechanical fix | lean-mend coverage |
|---|---|---|---|---|---|
| N | v4.34.0 [#14501](https://github.com/leanprover/lean4/pull/14501) | `if_pos`/`if_neg`/`dif_pos`/`dif_neg` renamed to `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`, with a deprecated alias kept. | deprecation warning today | Rename to the new lemma names. | Automatic, via the **derived** alias-map mechanism — no rule file needed while the alias survives. |
| O | v4.34.0 [#14462](https://github.com/leanprover/lean4/pull/14462) | `Nat.div_eq`→`Nat.div_eq_ite`, `Nat.mod_eq`→`Nat.mod_eq_ite`, alias kept. | deprecation warning today | Rename. | Automatic (**derived**), same as N. |
| P | v4.34.0 [#14412](https://github.com/leanprover/lean4/pull/14412) | `ExceptCpsT.runK` drops its unused `s : ε` parameter; **no alias is kept**. | `typeMismatch` (too many arguments) at every call site | Delete the extra argument at the call. | `none`; narrow (one function), needs a call-site argument-drop operation. |
| Q | v4.34.0 [#14294](https://github.com/leanprover/lean4/pull/14294) | `String.toList` loses `@[implicit_reducible]`, becoming semireducible. | a `simp`/`dsimp`/defeq check that relied on unfolding it stops firing | An explicit rewrite lemma, case-specific. | Same transparency family as row C/K; partially answerable by the same rules, not fully. |
| R | v4.35.0 [#14624](https://github.com/leanprover/lean4/pull/14624) (+[#14583](https://github.com/leanprover/lean4/pull/14583)) | Instance search now respects transparency on instance-implicit metavariable types. | an instance that used to be found is no longer found: `failed to synthesize` | `set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in`. | Same family as C/K; reinforces the need for the generalized operation in Part 3. |
| S | v4.35.0 [#14937](https://github.com/leanprover/lean4/pull/14937) | `rwa [rules] at h` now closes the goal only with `h` itself, not with any matching assumption. | `unsolved goals` (class `unsolvedGoals`) where `rwa` used to close via a different hypothesis | `rw [rules] at h; assumption` (or `<;> assumption` for the now-deprecated multi-location form). | `none`, but answerable with **existing** ops: see proposed rule below. |
| T | v4.35.0 [#14854](https://github.com/leanprover/lean4/pull/14854) | `constructor` now **warns** (does not error) when more than one constructor matches the goal, and always picks the first. | a new `linter.*` warning, which can land inside an unrelated candidate's edited bytes and block it under `docs/machine.md` structural check 4 | `constructor!` keeps the old silent behaviour. | `none`; cheap to add with the existing `keywordSwap` op. |
| U | v4.35.0 [#8309](https://github.com/leanprover/lean4/pull/8309) | `Decidable` is redefined as a `Bool`-carrying structure instead of a 2-constructor inductive (`isTrue`/`isFalse` remain usable as patterns). | `typeMismatch` for code that builds/destructures `Decidable` outside the `isTrue`/`isFalse` pattern forms | none generic | `none`; no safe mechanical fix identified. |
| V | v4.35.0 [#14727](https://github.com/leanprover/lean4/pull/14727) | Removes `Lean.Grind.ToInt` and the `BitVec`/`UIntN` E-matching lemmas it backed; removes `[grind ext]` from `Fin.ext`. | `grind` that used to close a `Fin`/`BitVec` goal now leaves it open (class `tacticFailed`/`unsolvedGoals`) | none generic | `none`; the replacement facts (homomorphism attributes) are case-specific. |
| W | v4.35.0 [#14953](https://github.com/leanprover/lean4/pull/14953) | Removes `Lean.reduceBool`, `Lean.reduceNat`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler`. | `unknown identifier` | the release note's own migration says: use `native_decide`. | **Impossible for lean-mend by design**: `native_decide` is in `forbiddenTokens` (decision D10, `LeanMend/Spec/Types.lean`). A fix must go to an agent/person (`docs/rules.md` §From residue to rule), never a rule. |

**Changes read but excluded**: v4.34.0 [#14215](https://github.com/leanprover/lean4/pull/14215) (`bv_normalize` internal `Sym.simp` move), [#14391](https://github.com/leanprover/lean4/pull/14391) (`Environment.replay` rename, alias kept, proof-checker tooling only), [#14523](https://github.com/leanprover/lean4/pull/14523) (`letFun` deprecated, alias kept), [#14479](https://github.com/leanprover/lean4/pull/14479) (`IO.Error.osCode`, runtime only), [#14538](https://github.com/leanprover/lean4/pull/14538) (`eq_false_of_ne_true` rename, alias kept); v4.35.0 [#14874](https://github.com/leanprover/lean4/pull/14874) (`mvcgen` deprecated, alias kept), [#15141](https://github.com/leanprover/lean4/pull/15141) (`lake cache put-staged` CLI), [#15054](https://github.com/leanprover/lean4/pull/15054) (range-notation precedence — a silent semantic change, not a build error), [#14350](https://github.com/leanprover/lean4/pull/14350) (singleton-notation indentation, a parse-format issue), [#15019](https://github.com/leanprover/lean4/pull/15019)/[#15020](https://github.com/leanprover/lean4/pull/15020) (macro-internal), [#14890](https://github.com/leanprover/lean4/pull/14890) (`Dyadic` lemma-name swap, narrow). v4.34.1 is a kernel/runtime soundness patch only (see its [release note](https://lean-lang.org/doc/reference/latest/releases/v4.34.1)).

### Proposed rules for the `none` rows that use only existing operations

```json
{
  "name": "binder-override-restriction",
  "class": "binderOverride",
  "entrenchment": "proposed",
  "provenance": {
    "evidence": "Lean v4.30.0 PR #12603 restricts a constructor's binder-kind override to parameters in the declaration header; a typeless binder that repeats a section `variable` name is read as a forbidden override."
  },
  "applies": { "after": "v4.29.0", "through": "v4.35.0" },
  "node": "any",
  "candidates": [ { "op": "typeAnnotation" } ]
}
```
This candidate already exists as `EditTarget.typeAnnotation` (decision D11,
`LeanMend/Spec/Types.lean`), gated behind `--annotate-binders`; no rule file
in `rules/proposed/` uses it today.

```json
{
  "name": "dead-dsimp-after-beta",
  "class": "simpNoProgress",
  "entrenchment": "proposed",
  "provenance": {
    "evidence": "Lean v4.31.0 PRs #13807 and #13528: the app elaborator now beta-reduces substituted arguments, so a `dsimp only` step that existed only to perform that reduction does nothing."
  },
  "applies": { "after": "v4.29.0", "through": "v4.35.0" },
  "node": "simp",
  "candidates": [ { "op": "deleteTactic" } ]
}
```

```json
{
  "name": "lean-rbmap-move",
  "class": "unknownIdentifier",
  "entrenchment": "proposed",
  "provenance": {
    "evidence": "Lean v4.32.0 PR #13908 deprecates Lean.RBMap/Lean.RBTree in favour of Std.TreeMap/Std.TreeSet, via a deprecated_module shim. Distinct from batteries-rbtree-move, which targets Batteries.RBMap only."
  },
  "applies": { "after": "v4.29.0", "through": "v4.35.0" },
  "node": "any",
  "candidates": [
    { "op": "renamePrefix", "old": "Lean.RBMap", "new": "Std.TreeMap" },
    { "op": "renamePrefix", "old": "Lean.RBTree", "new": "Std.TreeSet" }
  ]
}
```

```json
{
  "name": "rwa-single-hypothesis",
  "class": "unsolvedGoals",
  "entrenchment": "proposed",
  "provenance": {
    "evidence": "Lean v4.35.0 PR #14937 redesigns rwa: `rwa [rules] at h` now closes the goal only with h, not with any assumption that happens to match."
  },
  "applies": { "after": "v4.34.1", "through": "v4.35.0" },
  "node": "rw",
  "candidates": [
    { "op": "keywordSwap", "from_": "rwa", "to": "rw" },
    { "op": "appendTactic", "tactic": "assumption" }
  ]
}
```

### New operations the `none` rows need

- **`setOptionBefore (name value : String)`** — generalizes the existing
  `heartbeats n` (`LeanMend/Spec/Types.lean`): insert
  `set_option {name} {value} in` before the declaration (outside the
  statement region, like `beforeDecl`). This one operation answers row H
  (`backward.do.legacy true`), row L (`maxRecDepth <n>`), and row R
  (`backward.isDefEq.respectTransparency.instanceSearchTypes false`) — three
  unrelated release families, one operation. See Part 3.
- **A case-tag-aware rename** for row F: after `apply`/`rewrite` relabel a
  subgoal, rewrite the `case <oldTag> => …` that follows to the new tag name,
  reading both from the probe's goal-state output (`docs/machine.md`
  §Operands already records the goal state at a site).
- **An ascription rewrite** for row B: given a call `f A` to a named
  function `f` with one explicit argument, replace it with `(inferInstance :
  A)` — narrower than `replaceInBody` (no declaration name, no verbatim-once
  constraint), closer to `simpaToExact` in shape.

### EVMLean run-21 residue cross-check

For each rule, the most likely upstream cause, checked against
`git -C EVMLean diff fd4f5e6 bcca6b1`:

| Rule | Likely cause | Confidence |
|---|---|---|
| `simp-set-id-run` | Same transparency family as Table 1 row C: `simp` at `.reducible` transparency no longer unfolds `Id.run`. v4.30.0 [#12757](https://github.com/leanprover/lean4/pull/12757) marks `Id.run` `[implicit_reducible]`; v4.33.0 [#13637](https://github.com/leanprover/lean4/pull/13637) later splits what `implicit_reducible` grants. No release note states "`Id.run` left the default simp set" in those exact words — lean-mend's own `rules/proposed/simp-set-id-run.json` provenance field makes that specific claim and it is `[UNVERIFIED]` against the primary sources read here. | `[INFERENCE]`; recommend `lean-mend attribute` (bisection, `docs/rules.md` §Attribution by bisect) to pin the exact commit. |
| `close-bullet-tacticFailed` / `close-bullet-typeMismatch` | Not an upstream release change: the break is lean-mend's **own** earlier `matchToIf` edit reshaping `Gas.Ccallgas`'s `if`, which moves where `split` lands in the proof of `Ccallgas_lt_Ccall`. | Confirmed by the diff (`GasLemmas.lean`); self-induced cascade, not a Lean release symptom. |
| `simpa-hidden-mismatch` | Transparency family, row C/K: v4.33.0 #13895 makes strict transparency the default, which is exactly what exposes a hidden `Decidable`-instance difference that only `exact`'s looser check tolerates. | High; matches the family's documented symptom text verbatim. |
| `match-literal` | No release-note match found for a `Fin`/numeral `match`-pattern `Decidable` change in v4.30–v4.33. | `[UNVERIFIED]`; recommend bisection. |
| `evmlean-literal-zero` | No release-note match found. | `[UNVERIFIED]`; recommend bisection. |
| `evmlean-subtractGas-unfold` | Transparency family: v4.31.0's own migration guidance ("add the now-required projections explicitly to `simp`/`dsimp` calls") is *exactly* what the EVMLean hand bump did (three new `@[simp]` projection lemmas). | High. |
| `agent-evmlean-wheels-ofUInt256_ofNat` | Same `Id.run`/transparency family as `simp-set-id-run`, compounded with a `Fin` literal issue. | `[INFERENCE]`. |
| `batteries-rbtree-move` | Batteries PR #1792 (row X above). | Confirmed. |
| `fin-simp-mismatch` / `fin-simp-unsolved` | Transparency family: `Fin`'s `<`/`≤` coercion unfolding is a `def`, subject to the same `.reducible`-transparency regression as `Id.run`. | `[INFERENCE]`. |

For the five **open** residue classes, the human fix in `bcca6b1` reveals
gaps the existing 11 rules (even the proposed ones) do not close:

- **NoOutOfFuel 45/57/87** (typeMismatch): see § Corrections. On the run-21
  branch, `fin-simp-unsolved` appended `exact Fin.isLt _` at these sites,
  and that tactic fails inside its own bytes. The exposure guard (lea-e8e)
  now rejects such an edit. The hand fix is `simp [Id.run]`, the edit of
  `simp-set-id-run`.
- **NoOutOfFuel 215/217** (unsolvedGoals): the hand fix is
  `simp only [step, Id.run] at h <;> first | exact execBinOp_no_OutOfFuel _ _ h
  | exact execTriOp_no_OutOfFuel _ _ h | exact execUnOp_no_OutOfFuel _ _ h |
  simp_all [step]`. `appendTactic (tactic : String)` already accepts an
  arbitrary tactic string, so this needs **no new operation** — only a rule
  file with this literal text for `step_no_OutOfFuel`'s `StopArith`/`CompBit`
  cases. `rules/proposed/` has none.
- **ReturnDataBound 2354, 2397** (typeMismatch): the hand fix turns
  `simpa only [L] using g.val.isLt` into `simp only [L]` (on the goal, no
  `at`) followed by `exact g.val.isLt`. This is neither `simpaToExact`
  (drops the lemma list entirely) nor `simpaSplit` (wraps with `have`/`at
  … ⊢`). **No existing `EditOp` produces this exact shape.** Proposed new
  operation: `simpaToSimpExact` — `simpa [L] using T` becomes `simp only
  [L]` then `exact T`, keeping the lemma list, dropping only the `using`.
- **ReturnDataBound 3287**: the site is the `match pc with` →
  `match pc.val with` family already answered by `match-literal`/`valCompare`
  — but `match-literal`'s `class` is `missingDecidable`, and this site
  classifies as `typeMismatch`. The **same root cause surfaces under two
  different `ErrorClass`es** depending on how the match result is consumed,
  and lean-mend's one-class-per-rule schema misses the `typeMismatch`
  instances. Fix: a sibling rule file, same candidates, `class:
  "typeMismatch"`.
- **AccountLocality's four `· exact hXiAcc` sites**: two use the pattern
  `simp [...] at hXi ⊢; exact hXi` — already `simpaSplit`'s hypothesis case,
  so `simpa-hidden-mismatch` *attempts* these and evidently still fails in
  run 21 (candidate rejected, or a later linter/progress check blocks it).
  The other two use `simp only [sendEth, if_true, ne_eq, bne_iff_ne,
  ite_not]; exact hXiAcc` — the same `simpaToSimpExact` gap as
  ReturnDataBound above, this time on a hypothesis-less goal.

## Part 2: Learnings from related tools

### hopscotch

**What it repairs.** Build breaks in a downstream project across a range of
mathlib (or any dependency) commits. It does not edit Lean proof text at all:
its one automated repair class is an **import rewrite** —
`Hopscotch.AutoFix.Mathlib.ModuleDeprecation` — following the
`deprecated_module` shim chain a dependency leaves behind when it moves a
file. ([README](https://github.com/leanprover-community/hopscotch))

**How it decides an edit is accepted.** It does not decide at all by itself.
`detect` only proposes; nothing is applied until `hopscotch fix apply` runs,
and the fix's correctness is validated by the **next** build, not by
hopscotch
([`Framework.lean`](https://raw.githubusercontent.com/leanprover-community/hopscotch/main/Hopscotch/AutoFix/Framework.lean)).
This is a weaker acceptance bar than lean-mend's: lean-mend's `Accepted`
structure (`LeanMend/Spec/Types.lean`) requires progress, a clean candidate,
and zero linter warnings in the edited bytes, proved as part of the same
transition that applies the edit.

**Data model.** One record, `ImportMigration`
(`oldModule`, `newModules : Array String`, `partialFix : Bool`, `note :
String`), fix-agnostic and JSON-serializable
([`Migration.lean`](https://raw.githubusercontent.com/leanprover-community/hopscotch/main/Hopscotch/AutoFix/Migration.lean)).
Far simpler than lean-mend's `Candidate`/`EditOp`, because the only shape of
edit it ever proposes is "replace an import list."

**How it reports results.** Two buckets, both computed once at run
conclusion and both persisted to `results.json`: `proposedFixes` (repairs the
boundary that stopped the run) and `deprecatedImports` (imports that build
today through a live shim but will break later — recorded even on a fully
green run). ([`docs/autofix-scenarios.md`](https://raw.githubusercontent.com/leanprover-community/hopscotch/main/docs/autofix-scenarios.md))

**Stated limits.** Refactor-renames (upstream deleted the old declaration
content, not just moved it) need a human; warnings-as-error regimes still
need the `@[deprecated]` declaration-name renames in the same PR; network
degradation silently falls back to a plain culprit report; a format change in
Lean's deprecation-warning text silently degrades two of twelve detection
scenarios, never to a wrong answer.
([`docs/autofix-scenarios.md`](https://raw.githubusercontent.com/leanprover-community/hopscotch/main/docs/autofix-scenarios.md)
§Known limitations)

### downstream-reports

**What it does.** A scheduled CI harness around hopscotch: twice daily it
builds every registered downstream against mathlib's newest commit, bisects
on failure, and publishes two commits per project — the last-known-good
(LKG) and first-known-bad (FKB), which are adjacent by construction.
([README](https://github.com/leanprover-community/downstream-reports))

**How it reports results.** A public status page plus four composite GitHub
Actions a downstream calls from its own CI: `bump-to-latest` (move the pin to
LKG and rebuild to confirm), `open-bump-pr`, `query-latest` (read-only), and
`track-incompatibility` (open/close an issue while a regression is active).

**Stated limits.** The service validates only the mathlib dependency; a
registered project whose pin falls far behind produces "a low quality
signal."

### AXLE `repair_proofs`

**What it repairs.** Seven independent, declaration-local passes:
`insert_sorries`, `remove_extraneous_tactics`, `apply_terminal_tactics`
(tries a fixed tactic list, default `["grind"]"`, at every open goal),
`replace_unsafe_tactics` (`native_decide` → `decide +kernel`),
`remove_unknown_options`, `enable_autoImplicit`, `relax_defeq_transparency`.
([`docs/tools/repair_proofs.md`](https://raw.githubusercontent.com/AxiomMath/axiom-lean-engine/main/docs/tools/repair_proofs.md))

**How it decides an edit is accepted.** `okay = True` only when every
requested repair succeeds **and** the repaired file compiles; a repair that
was detected as necessary but could not be completed (an un-provable
`sorry`, an unreplaceable `native_decide`) is a `tool_messages` error, not a
silent partial success
([CHANGELOG v1.4.0](https://raw.githubusercontent.com/AxiomMath/axiom-lean-engine/main/CHANGELOG.md)).
This is a binary "compiles or not" bar — weaker than lean-mend's, which also
certifies the statement and axiom set are unchanged
(`docs/machine.md` §The invariant).

**Data model.** No persisted rule or candidate record at all: each repair is
a direct text transformation inside one request/response round trip; nothing
is reused across requests.

**Stated limits.** `repair_proofs`'s own doc says plainly: "does not
guarantee that repaired proofs will be semantically correct or complete,"
"some repairs may introduce new errors or conflicts." `insert_sorries` and
`apply_terminal_tactics`-closing-with-`sorry`-replacement are explicitly
outside anything lean-mend may do (decision D10 forbids the token `sorry`
unconditionally).

**`relax_defeq_transparency`, independently.** AXLE's documented repair for
Lean ≥ 4.29 is to prepend `set_option backward.isDefEq.respectTransparency
false in` "when the fix gets the proof further (all errors resolved, or the
first error appears later in the source)" — the acceptance rule is
structurally identical to lean-mend's own progress check
(`docs/machine.md` §Transitions, the `mend` row). This is independent,
cross-tool confirmation (AXLE has no connection to lean-mend) that the
transparency-discipline family (Part 1, row C/K) is answered by exactly the
scoped-option-insertion shape lean-mend already uses for `heartbeats`.

**The technical report.** [arXiv:2606.26442](https://arxiv.org/abs/2606.26442)
("AXLE: A Cloud Infrastructure for Lean 4 Theorem Proving Utilities") frames
AXLE as throughput infrastructure for AI-proving pipelines (500M+ requests
served) rather than a toolchain-bump tool; it is not about breaking-change
repair as a topic, so it adds no further evidence beyond the CHANGELOG and
tool doc already cited. `[UNVERIFIED]` beyond the abstract: the report's
inner technical content was not read in full.

### Concrete learnings for lean-mend

1. **A `setOptionBefore` operation, not just `heartbeats`.** Evidence: Part
   1 rows H, L, R, and AXLE's `relax_defeq_transparency` all resolve to one
   shape — insert `set_option <name> <value> in` before a declaration. File:
   `LeanMend/Spec/Types.lean` (`EditOp` inductive); generalizes the existing
   `heartbeats (n : Nat)` constructor.
2. **Module-deprecation migration — lean-mend does not do this today.**
   `batteries-rbtree-move` hand-encodes one case of exactly the pattern
   hopscotch's `Hopscotch.AutoFix.Mathlib.ModuleDeprecation` resolves
   generically: read a `deprecated_module` shim's import list (not just its
   `@[deprecated]` *declaration* aliases, which is all `docs/rules.md`
   §Entrenchment-and-order item 1 covers today) and rewrite the importing
   file's `import` line to match. lean-mend's alias-map mechanism
   (`AliasMap`, `LeanMend/Spec/Types.lean`) only resolves *declaration*
   deprecations found via `#print` of `@[deprecated]`; it has no equivalent
   probe for a *module-level* `deprecated_module` shim's `import` list.
   `Lean.RBMap`/`Lean.RBTree` (Table 2, row J) is the next instance of this
   exact class lean-mend will meet.
3. **An advisory/proposal split, borrowed from hopscotch.**
   `docs/rules.md` has three `entrenchment`s (`derived`, `ratified`,
   `proposed`) but no "builds today, will break later" state. hopscotch's
   `deprecatedImports` bucket is exactly the EVMLean-pre-v4.33.1 situation
   (a `Batteries.RBMap` import that still built, through a shim, before the
   shim was deleted): catching it **before** the bump run — by scanning the
   target's current imports against the new toolchain's deprecation list —
   turns a future 2–3 hour run's first failure into a pre-flight warning.
   This directly serves the operator's stated goal (`docs/machine.md` is
   silent on any pre-bump scan today; `LeanMend/Core/Run.lean`'s state
   machine starts at `idle` with only "the target path," no advisory phase).
4. **Bisection to one breaking commit — already adopted, refine the
   session model.** `docs/rules.md` §Attribution by bisect already cites
   hopscotch's binary-search method by name. hopscotch's documented
   refinements that lean-mend's docs do not yet describe: a persisted,
   resumable session per project (`.lake/hopscotch/state.json`), a
   git-cleanliness guard before resuming or starting a bisect (an
   uncommitted fix silently skews every later probe), and `--keep-last-good`
   to leave the tree in a known-buildable state after the search. Tie to
   `docs/rules.md` §Attribution by bisect and the (not-yet-written) shell
   code for `lean-mend attribute`.
5. **A fix catalogue derived from upstream data, like hopscotch's shim
   survey.** hopscotch's `docs/autofix-scenarios.md` cites measured figures
   from "all 164 shims on mathlib master" (median deprecation window 42
   commits, up to ~2065). lean-mend's `rules/proposed/` today is built
   entirely from two hand runs (EquiVM, EVMLean). A similar survey of every
   Batteries/Lean-core `deprecated_module` and `@[deprecated]` declaration
   active in the v4.29.0–v4.35.0 window would turn Part 1's `[INFERENCE]`
   and `[UNVERIFIED]` rows into confirmed, bisected `provenance.introduced_by`
   entries before the next EVMLean or EquiVM run meets them — the explicit
   aim of this research.

## Part 3: Summary

**v4.30.0–v4.33.1 (12 breaking changes surveyed with a downstream source
symptom: rows A, B, C/K-family, D, E, F, G, H, I, J, L, X):**
- Already covered by an existing checked-in rule: **2** (`X`, fully, via
  `batteries-rbtree-move`; the `C/K` transparency family, partially, via
  `simpa-hidden-mismatch` and `evmlean-subtractGas-unfold` — the EVMLean
  run-21 residue shows this family is not fully closed).
- Would be covered by a new rule file using only **existing** `EditOp`s:
  **3** (`A` via the existing `typeAnnotation` target, `D` via `deleteTactic`,
  `J` via `renamePrefix`).
- Need a **new** operation: **3 rows** (`B`, `F`, `H`/`L` together), answered
  by **3 distinct new operations** (an ascription rewrite, a case-tag
  rename, and `setOptionBefore` — the last covers both `H` and `L`, plus `R`
  in the next range).
- No safe generic mechanical fix (human judgement required): **1** (`E`),
  plus `G` which depends on an `[UNVERIFIED]` fact (whether an alias
  survives).

**v4.34.0–v4.35.0 (10 breaking changes surveyed with a downstream source
symptom: rows N, O, P, Q, R, S, T, U, V, W):**
- Already covered by an existing checked-in rule: **0** (every current rule's
  `applies.through` stops at `v4.33.1`).
- Automatically covered without a new rule file (derived alias mechanism,
  while the alias survives): **2** (`N`, `O`).
- Would be covered by a new rule file using only **existing** `EditOp`s:
  **2** (`S`, the `rwa` redesign, via `keywordSwap`+`appendTactic`; `T`, the
  `constructor` warning, via `keywordSwap`).
- Need a new operation: **2 rows** (`P`, narrow; `R`, reuses the
  `setOptionBefore` operation proposed for the prior range).
- No safe generic mechanical fix, or impossible by design: **3** (`U`, `V`;
  and `W`, which is not merely unaddressed — decision D10's `forbiddenTokens`
  makes the documented upstream fix, `native_decide`, a token lean-mend can
  never emit).

**The three highest-value additions to lean-mend, with evidence:**

1. **A `setOptionBefore (name value : String)` `EditOp`**, generalizing the
   existing `heartbeats n`. Evidence: it is the one mechanical answer to
   three unrelated release families — the transparency-discipline default
   flip (v4.33.0 [#13895](https://github.com/leanprover/lean4/pull/13895),
   tightened again by v4.35.0 [#14624](https://github.com/leanprover/lean4/pull/14624)),
   the deterministic kernel-recursion bound (v4.33.0
   [#13956](https://github.com/leanprover/lean4/pull/13956),
   `set_option maxRecDepth`), and the new-`do`-elaborator default (v4.32.0
   [#13305](https://github.com/leanprover/lean4/pull/13305),
   `backward.do.legacy`) — and it is independently confirmed by AXLE's
   `relax_defeq_transparency` repair, a tool with no connection to
   lean-mend, converging on the same shape.
2. **A `rules/proposed/rwa-single-hypothesis.json` rule using only existing
   ops** (`keywordSwap "rwa" "rw"` then `appendTactic "assumption"`).
   Evidence: v4.35.0 [#14937](https://github.com/leanprover/lean4/pull/14937)
   redesigns `rwa` to drop its old "try any assumption" fallback, which
   `classify` sees as `unsolvedGoals`; v4.35.0 is explicitly EquiVM's and
   EVMLean's **next** target per this task's brief, so this break is not
   hypothetical — it is scheduled.
3. **A `simpaToSimpExact` `EditOp`**: `simpa [L] using T` becomes `simp only
   [L]` then `exact T`, keeping the lemma list, unlike `simpaToExact` (drops
   it) or `simpaSplit` (wraps with `have`/`at … ⊢`). Evidence: this is the
   exact shape of the human fix at **three of the five still-open** EVMLean
   run-21 residue sites — `ReturnDataBound.lean` 2354, 2397, and two of
   `AccountLocality.lean`'s four `· exact hXiAcc` sites (git diff
   `fd4f5e6..bcca6b1`) — making it the one `EditOp` gap directly blocking
   today's open residue, not a future one.

## Corrections

The operator checked these claims after the subagent finished.

- Confirmed: v4.33.0 #13895 "enables the
  backward.isDefEq.respectTransparency.types option by default" (release
  notes, v4.33.0).
- Confirmed: the hand bump `bcca6b1` changed `simpa only [L] using
  g.val.isLt` to `simp only [L]` followed by `exact g.val.isLt` at
  `ReturnDataBound` 2354 and 2397.
- Confirmed: v4.35.0 #14937 makes `rwa [rules] at h` close the main goal
  with `h` only.
- Corrected: `NoOutOfFuel` 45, 57 and 87 were not answered by
  `simp-set-id-run` in run 21. Three commits on the run-21 branch appended
  `exact Fin.isLt _` there, which fails in its own bytes. Together with the
  four `· omega` edits in `AccountLocality`, 7 of run 21's 12 residue sites
  came from that one lean-mend defect, fixed by lea-e8e.
- Dropped: row T (`constructor` warns when several constructors match,
  v4.35.0 #14854). lean-mend repairs error sites only, and the change is a
  warning, so a rule for it never triggers.

## Decisions

B1. lean-mend has one operation `setOptionBefore name value`, which puts `set_option name value in` before a declaration, and it replaces `heartbeats n`.
B2. A rule whose operations are all `setOptionBefore` runs after every other rule of its entrenchment, because an option hides a change instead of adapting the source.
B3. lean-mend has rules that answer the transparency default (v4.33.0 #13895), the kernel recursion bound (v4.33.0 #13956) and the new do elaborator (v4.32.0 #13305) with `setOptionBefore`.
B4. lean-mend has one operation `simpaToSimpExact`, which turns `simpa [L] using T` into `simp [L]` followed by `exact T` and keeps the `only` modifier and the lemma list.
B5. A rule's `class` field accepts a list of error classes, so one rule answers one root cause under every class Lean reports it as.
B6. The rule `match-literal` lists the classes `missingDecidable` and `typeMismatch`.
B7. lean-mend has a rule for v4.35.0 #14937 that turns `rwa [rules] at h` into `rw [rules] at h` followed by `assumption`.
