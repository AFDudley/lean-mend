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
  "name": "batteries-rbmap-moved",
  "class": "unknownIdentifier",
  "entrenchment": "ratified",
  "provenance": {
    "judgment": { "by": "afd", "card": "c-0007", "at": "2026-10-23T12:00:00Z" },
    "introduced_by": { "package": "batteries", "commit": "<sha>" }
  },
  "applies": { "after": "v4.29.0", "through": "v4.33.1" },
  "pattern": { "node": "ident", "name": "Batteries.RBMap" },
  "candidates": [
    { "replace": "Batteries.RBTree.RBMap" }
  ]
}
```

| Field | Meaning |
|---|---|
| `class` | the `ErrorClass` constructor the rule answers |
| `entrenchment` | `ratified` or `proposed`; `derived` rules are never files |
| `provenance` | the judgment that ratified the rule, and the upstream change that caused the class |
| `applies` | the toolchain window in which the rule is valid, from the attribution |
| `pattern` | the syntax node kind and the fields to match; antiquotations bind parts of the node |
| `candidates` | replacements, in the order to try; each is Lean syntax with antiquotations |

A candidate is syntax, not text (brief item 5). Before an attempt, the probe
parses the candidate at the node's syntax category under the target toolchain.
A candidate that does not parse is rejected without a build.

The rule loader refuses a vacuous rule (concept C9): a pattern that matches
every node of its kind with no field constraint, a candidate list that is
empty, or a candidate that only deletes the node.

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
2. **Ratified** rules, in file-name order inside one class.
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

The agent returns an edit, and may return a rule. The fixed runner, which the
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
