# Handoff: lean-mend

Written 2026-11-21 by session `01a1f9a0`.

## What is to be done

1. **Qualify every use of "gate" in `docs/process.md`** (14 uses at `integrated` `3337433e`, among them the table
   column "Gate"). A gate is one check that runs; a decision that a person or an agent makes is a judgment, not a gate;
   "gate" is not a verb (`glossary.md`, "gate" and "judgment").
2. **Open work 1 of `docs/labbook/2026-11-19-subtree-sync-repair.md` is still open.** armada-laconic-mono (formerly
   evm-proof-toolchain) merged on 2026-11-20, and its subtree sync refused `lean-mend/`: the newest subtree commit
   there, `e952f764`, has no `git-subtree-split` trailer. The repair is item 1 of the armada-laconic-mono handoff.
   Until it is done, the monorepo's `lean-mend/` has `docs/glossary.md` at the old path.
3. **Seven pebbles stay open:** `lea-5eb`, `lea-01a`, `lea-c4e`, `lea-830`, `lea-342`, `lea-9c8`, `lea-935`. Their
   work is not done (handoff of 2026-11-19). `lea-5eb` stays open until its spec runs against `integrated`:
   `setOptionBefore` exists in `LeanMend/Core/Cause.lean`, but the history before the subtree marker `899a4cd` does
   not show whether B1 to B3 are complete.

## State

- `integrated` and `main` are `3337433e` on GitHub, so open work 2 of the labbook entry is done.
- Open work 3 and 4 of the same entry are still open: the unconfirmed EBUSY report, and the branches left from the
  repair.
- `.scratch/uncommitted-2026-11-19.diff` is a backup of the old uncommitted bus changes.
