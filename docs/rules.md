# Rules

A rule is data (brief item 3). It maps an error class and a syntax pattern to
an ordered list of candidates. Code never encodes a repair; code only loads,
orders and applies rules.

## The rule format

One JSON file per rule, in `rules/` for ratified rules and in
`rules/proposed/` for proposed rules. The shell parses each file into a typed
`Rule` once (concept B2). A file that does not parse stops the run.

```json
{
  "name": "simp-set-pure",
  "class": "typeMismatch",
  "entrenchment": "ratified",
  "provenance": {
    "judgment": { "by": "afd", "card": "c-0007", "at": "2026-10-23T12:00:00Z" },
    "evidence": "EquiVM lean-v4.33.1 report §13.3, §14.1 (ExternalCall 530, 543)",
    "introduced_by": { "package": "lean4", "commit": "<sha>" }
  },
  "applies": { "after": "v4.29.0", "through": "v4.33.1" },
  "node": "simp",
  "candidates": [
    { "op": "simpArgAdd", "lemma": "pure" },
    { "op": "simpArgAdd", "lemma": "Option.bind" }
  ]
}
```

| Field | Meaning |
|---|---|
| `class` | the `ErrorClass` constructor the rule answers |
| `entrenchment` | `ratified` or `proposed`; `derived` rules are never files |
| `provenance` | the judgment that ratified the rule, the evidence, and the upstream change that caused the class |
| `applies` | the toolchain window in which the rule is valid, from the attribution |
| `node` | the tactic family the site's node must belong to: `simp` (`simp`, `simp only`, `simpa`, `dsimp`, `simp_all`), `rw` (`rw`, `rewrite`, `erw`), `exact`, `decide`, or `any` |
| `candidates` | edit operations, in the order to try |

### Edit operations

A candidate is not free text and not a regular expression. It is one
constructor of a closed Lean inductive type, `EditOp`. The type checker then
forces every function over candidates to handle every operation (concept B4).
Each operation reads the syntax node that the probe's `node` command returns
for the site, and writes a replacement for that node's byte range only
(brief item 5). The EquiVM v4.29.0 → v4.33.1 hand repairs (report §13.3,
§14.1, §14.3) are all of these forms:

| `op` | Effect on the node | EquiVM evidence |
|---|---|---|
| `rename` | replace a name with another (the derived alias rules) | the Batteries `RBMap` move |
| `simpArgAdd` `lemma` | add `lemma` to the `[…]` list of a `simp`-family tactic, or add `[lemma]` if it has none | `pure` (530, 543), `Bool.and_self` (294, 365), `Option.option` (six sites), `Fin.getElem_fin`, the `U256_TONAT` set |
| `simpaToExact` | `simpa […] using T` becomes `exact T` | the pc-sum defeq class (§14.3), `default : UInt256` |
| `keywordSwap` `from` `to` | replace the tactic keyword | `rw` → `erw` (§13.3) |
| `deleteTactic` | remove the tactic | the no-op `dsimp only at h`; a trailing `decide +kernel` after the goal is closed |
| `appendTactic` `tactic` | insert `tactic` after the node, on its own line at the node's column, to close the goal the node leaves | EVMLean `Wheels.lean` 53 and 99: `simp [UInt256.size, …]` leaves `↑x < 2^256`; the hand repair was `simpa [...] using val.val.isLt`, which names a local variable; `exact Fin.isLt _` is the same step without the name |
| `renamePrefix` `old` `new` | a namespace move with no `@[deprecated]` aliases: every identifier in the file that starts with the name `old` (whole components) gets `new`, in one edit. Any site whose message names a moved name triggers it, whatever its class. A per-site rename failed on EVMLean: renaming a lemma's statement let Lean check its proof, which still had the old names, so the error count did not fall. A declaration that the target itself declares under the moved prefix (EVMLean: `def Batteries.RBMap.partition`) is renamed too, and gets an exact alias, so `compare` finds it | Batteries v4.33.1 moved `Batteries.RBMap`, `RBSet`, `RBNode` to `RBTree.*`; `Batteries.Data.RBMap` is a `deprecated_module` with no per-name aliases |
| `replaceInBody` `decl` `old` `new` | in declaration `decl`, replace text `old`, which must occur exactly once in its body, with `new` | the form of an agent's residue repair (§ From residue to rule) |
| `heartbeats` `n` | put `set_option maxHeartbeats n in` before the declaration | the deep pc reaches (§14.3 limit) |

An operation that does not apply to the node (for example `simpaToExact` on a
node that is not `simpa … using`) gives no candidate. It is not an error.

Before an attempt, the probe parses the replacement at the node's syntax
category under the target toolchain. A replacement that does not parse is
rejected without a build.

The rule loader refuses a vacuous rule (concept C9): an empty candidate list,
or `node` `any` with no `class` other than `unknown`. `deleteTactic` is allowed
only in a rule whose class is `simpNoProgress` or `noGoals` (text
`No goals to be solved`). Deleting a tactic that does nothing cannot weaken
a proof: the kernel still checks the result, and `sorry` stays forbidden
(structural check 2 in [machine.md](machine.md)).

The `split_ifs <;> rfl` case (§13.1, two branches with different `Decidable`
instances) has no operation. It stays residue for an agent.

## Entrenchment and order

For one site, the candidates come from every matching rule, in this order
(concept C3):

1. **Derived** rules. The alias map makes one rule per deprecated name: replace
   the old name with the final new name (brief item 4). A chain `a → b → c`
   resolves to `a → c`. A cycle is the refusal `AliasCycle`.

   The new toolchain alone is not a sufficient source. A deprecated alias
   makes a warning, not an error, while it exists. Lean, Batteries and
   Mathlib delete aliases some months later, and only then does the use fail.
   A bump across several releases therefore meets errors whose aliases exist
   only in the releases between the old and the new pin. The probe runs
   `deprecated` at each of those releases, and the map is the union.
2. **Ratified** rules, in file-name order inside one class. Inside a rule, the
   candidate order is the rule author's preference among valid repairs, and a
   person ratifies that order on the rule's Spec card. Prefer, in this order:
   1. a named lemma (`simpArgAdd` with the specific lemma), which is stable
      across releases and states the reason for the step;
   2. `simpaToExact`, which is valid but depends on definitional unfolding
      that a later release can change;
   3. `keywordSwap` `rw` → `erw`, which hides a mismatch instead of fixing it;
   4. `heartbeats`, which hides a cost regression upstream.

   Lean's linters are the check on this order: a candidate that causes a
   linter warning in its own bytes is rejected even if it builds
   ([machine.md](machine.md), structural check 4).
3. **Proposed** rules, only if the run sets `--with-proposed`. A patch from a
   proposed rule gets a card.

## The first error classes

The EquiVM v4.29.0 → v4.33.1 report (§13.3, §14.3) and the Goedel workbook
give the first classes. Each needs one fixture under `tests/fixtures/` that
shows the break and its repair.

| Class | Typical diagnostic | Typical candidates |
|---|---|---|
| `unknownIdentifier` | kind `lean.unknownIdentifier._namedError`; text `Unknown identifier` / `unknown constant` | the alias target; a moved name from a rule |
| `unknownNamespace` | text `unknown namespace` in `open` | the moved namespace |
| `missingDecidable` | kind `lean.synthInstanceFailed._namedError` with `Decidable` in the text | `match` on `p.val`; an `if` with `decide` |
| `typeMismatch` | text `Type mismatch`, for example between the literal forms `UInt256.ofNat N` and `{ val := N }`, or between `↑i` and `i.val` for `Fin` | literal forms: `rfl` → `by decide`, `show` with the other form, `simp only` with the constructor lemma; `Fin`: `Fin.val_cast_of_lt`, explicit `.val` |
| `simpNoProgress` | text `` `simp` made no progress `` | `simp [Id.run]`; the named lemma that left the default set |
| `unsolvedGoals` | kind `Tactic.unsolvedGoals` | the tactic with the lemma set from a rule; `first | … | …` chains |
| `noGoals` | text `No goals to be solved`: a tactic after the goal is closed | `deleteTactic` (EquiVM: a trailing `decide +kernel`) |
| `heartbeat` | kind `runtime.maxHeartbeats` | `set_option maxHeartbeats N in`, with N from the rule |
| `wallclock` | a timeout without `deterministic` | no candidates; see [machine.md](machine.md) |
| `unknown` | anything else | no candidates; residue |

`typeMismatch` is one class, not two. The diagnostic text alone does not
separate a literal-form mismatch from a `Fin` coercion mismatch. The rule
patterns separate them, by the syntax node at the site (concept B9).

`classify` is a pure function of the diagnostic. Lean's message `kind`
decides first, because it does not depend on wording. Where Lean names no kind
(`[anonymous]`), the text decides, compared without case. The first version
compared lowercase text only and put three classes into `unknown`, because Lean
prints `Unknown identifier`, `Type mismatch` and `` `simp` made no progress ``.
`tests/fixtures/diagnostics/` holds the real output of v4.29.0 and v4.35.0,
and `tests/ClassifyTest.lean` checks every class against it. `classify` does not
use the rule set. A class with no rules is still a class.

## Attribution by bisect

Brief item 9. For each class that appears in a run, lean-mend can find the
upstream commit that introduced it. The command is
`lean-mend attribute <target> <site>`. It is not on the main path, because it
builds the dependency many times.

1. The range is the dependency revisions between the old and the new manifest:
   Lean releases and nightlies, or Mathlib and Batteries commits.
2. The test at each revision is: build the site's module with its imports, and
   check whether the site's diagnostic has the same class. Mathlib revisions
   use `lake exe cache get`, so only the target modules build.
3. Bisection follows the method of hopscotch (`lean-hopscotch`): binary search,
   with a revision that does not build treated as unknown, not as good or bad.
4. The result goes into the rule's `provenance.introduced_by` and its
   `applies.after`. A card shows it.

## From residue to rule

Brief item 10. A residue site goes to an agent or a person as a residue packet:

- the site: module, byte range, syntax node, region;
- the class and the diagnostic;
- the goal state at the site, from the probe;
- every candidate that was tried, with its rebuild diagnostics;
- the rules that matched.

The agent returns its edit as a proposed rule file with one `replaceInBody`
operation: the declaration, the exact old text, and the new text. It may also
return a general rule. The EVMLean test used this path for
`Ethereum.AccountAddress.ofUInt256_ofNat` (`Wheels.lean` 81), with the hand
bump's repair as the agent's answer: no rule candidate closed that goal, and
the module is imported by almost every other module, so its residue blocked
the whole run. The fixed runner, which the
agent does not control (concept C4), then does this:

1. It applies the edit as an attempt, with the same structural checks, rebuild
   and invariant check as any candidate. If the attempt is accepted, it is
   committed with the provenance `ByAgent{session}`.
2. If the agent returned a rule, the runner loads it (with the vacuity check),
   and checks that the rule produces the agent's edit at this site.
3. The runner applies the rule to every other residue site of the same class,
   in attempt worktrees, and records each verdict.
4. The runner writes the rule to `rules/proposed/` in the lean-mend source,
   on a branch, and issues a **Spec** card with the verdicts.

A person ratifies the rule on the card. Ratification moves the file to
`rules/` and sets `entrenchment` to `ratified`. No count of successes ratifies
a rule by itself (concept C10).
