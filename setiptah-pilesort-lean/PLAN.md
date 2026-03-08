# Plan

## Cleanup: remove old FormulaWord machinery

The following are no longer on the proof path of `formulaWord_correct` and can be
deleted from `FormulaWord.lean` (and `formulaState` from `Reduction.lean`):

- **Adapters:** `clauseWord_start_sat_rep`, `next_correct_rep`, `clauseWord_start_nonsat_rep`
- **formulaState machinery:** `clauseNext_sat`, `formulaState_forward`, `clauseNext_advance`,
  `formulaState_penalty`, `formulaState_penalty_start`, `formulaState_penalty_all`,
  `virtualPileTypes_replicate_Q_cons'`, `formulaState_eq`
- **Superseded pos lemmas:** `formulaWord_sat_pos`, `formulaWord_unsat_pos`
- **Definition:** `formulaState` in `Reduction.lean`

`not_satisfiesFormula_rest` must stay (used in `formulaWord_unsat_pos'`).

The sorry lemma `testChain_sat_end_lt_new` in `ClauseWord.lean` is a dead end —
not in the proof path of `formulaWord_correct`.

## Cleanup: ClauseWord.lean _old lemmas

`testChain_nactd_old`, `testChain_nactd_end_old`, `testChain_sat_end_eq_old`
are still in use — check whether they can now be deleted.

## TODO

- **Rework `EndActivation.lean`** analogously to `Activation.lean`: replace
  `endActivationProp` + omnibus `end_activation_correct` with three split lemmas
  by starting position (`end_activation_correct_actd`, `_nactd`, `_disq`), using
  membership hypothesis `{w} (hw : w ∈ [ENDPOS, ENDNEG, ENDDK])`. Then update
  `endTestWord_consumption_*` in `TestConsume.lean` to use the named lemmas
  (eliminating the inline `have gadget := by decide` blocks).
