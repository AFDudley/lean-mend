/-! S1b (`docs/parallel.md` X3, X5): `tests/expose.sh` breaks this module, then
runs lean-mend with the rule in `rules/`. The rule fixes the head error and
exposes two later errors in the same declaration, at a byte reach smaller than
the old head's, so the Core accepts the edit. The padding comment is part of
the text the rule replaces: it gives the old head room to advance past. -/
theorem foo : True ∧ True := by
  exact unknownHead
  -- padding to inflate reach so the exposing edit can still advance
  done
