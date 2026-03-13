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

## New file: TestChain.lean

Create `TestChain.lean` to hold three consumption-form lemmas governing the
position reached by a sequence of test words (no endTestWord), one per starting
state. Each should be proved using only the corresponding individual lemma from
`TestConsume.lean` (`testWord_consumption_actd`, `_nactd`, `_disq`). The file
may eventually be merged into `TestConsume.lean`, but is kept separate for now.

### ACTD
Move `testChain_actd_cons` here (already in the right A1++A2 consumption form).

### CLAUSE\_DISQ
New A1++A2 consumption form of `testChain_disq` (which currently uses the old
`types.drop k` style). Statement:

```
applyWord (testWords ++ suffix) (compile (vpt ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
  A1.length * m + applyWord suffix (compile (vpt ALIGN A2)) CLAUSE_DISQ
```

### NACTD
New combined lemma covering all cases (activation or not). Proposed statement:

```
applyWord (testWords ++ suffix) (compile (vpt ALIGN (A1 ++ A2))) NACTD =
  A1.length * m + applyWord suffix (compile (vpt ALIGN A2))
    (if ∃ i : Fin A1.length, matchesLiteral A1[i] (start + i) clause
     then ACTD else NACTD)
```

Proof by induction on A1: base trivial; inductive step applies
`testWord_consumption_nactd` for the head, then either `testChain_actd_cons`
(if activated) or the IH (if not), with the existential managed across the
case split. If the existential form proves awkward at call sites, fall back to
two separate lemmas (no-activation and activation-at-i₀).

## Step 2: clauseWord consumption-form lemmas

Re-prove (or prove anew) the two clauseWord consumption-form lemmas using only
the clean building blocks: `start_clause_*`, TestChain lemmas, and the
individual `endTestWord_consumption_*` lemmas. The existing
`clauseWord_start_consumption` and `clauseWord_chain_consumption` in
`ClauseWordCorrect.lean` are the target statements; the goal is to simplify
their proofs.

### Prerequisites (already exist)

`start_clause_start` and `start_clause_disq` in `StartClause.lean` are the
single-origin consumption-form lemmas for the START_CLAUSE gadget — proved via
`gadget_lift_*` + `decide`. No changes needed there.

### clauseWord from START_POS (`clauseWord_start_consumption`)

Proof structure:
1. `start_clause_start` → suffix sees machine from NACTD
2. NACTD TestChain lemma → suffix sees A2 from ACTD (sat) or NACTD (nonsat)
3. `endTestWord_consumption_nactd` (sat/nonsat) or `endTestWord_consumption_actd`

Note: the current proof uses a classical case split (`HasMatchingAssignment`)
and `satisfiesClause_first_matchesLiteral` to find the first activation index.
This logic will need to connect to the existential in the NACTD TestChain lemma.

### clauseWord from CHAIN_DISQ (`clauseWord_chain_consumption`)

Proof structure:
1. `start_clause_disq` → suffix sees machine from ≥ CLAUSE_DISQ
2. CLAUSE_DISQ TestChain lemma → suffix sees A2 from ≥ CLAUSE_DISQ
3. `endTestWord_consumption_disq`

Note: `applyWord_mono` bridges the `≥ CLAUSE_DISQ` output of `start_clause_disq`
into the CLAUSE_DISQ TestChain lemma — same pattern as the current proof.

## Step 3: clauseNext consumption-form lemmas

Re-prove (or prove anew) the three `clauseNext` consumption-form lemmas in
`FormulaWordNew.lean` using only the clauseWord consumption lemmas from Step 2.
The target lemmas are:

- `clauseNext_good_consumption` (from START_POS)
- `clauseNext_bad_consumption` (from START_POS, unsatisfied clause)
- `clauseNext_chain_consumption` (from CHAIN_DISQ)

Each should reduce to a single `clauseWord_start_consumption` or
`clauseWord_chain_consumption` application (from Step 2), plus arithmetic.

## Step 4: Cleanup / deletion

Once Steps 1–3 are complete and the build passes, delete all dead code that is
no longer on the proof path of `formulaWord_correct`:

- Everything listed under "Cleanup: remove old FormulaWord machinery" above
- `testChain_nactd_old`, `testChain_nactd_end_old`, `testChain_sat_end_eq_old`
  in `ClauseWord.lean` (check uses first)
- Any remaining uses of bundled `testWord_consumption` / `endTestWord_consumption`
  (already eliminated, but confirm the definitions can be deleted too)
- Any other lemmas rendered unreachable by the new proof stack

---

## Progress

- [ ] **Step 1a** — Move `testChain_actd_cons` to `TestChain.lean`
- [ ] **Step 1b** — New `testChain_disq` (A1++A2 form) in `TestChain.lean`
- [ ] **Step 1c** — New combined `testChain_nactd` in `TestChain.lean`
- [ ] **Step 2a** — Re-prove `clauseWord_start_consumption` using Step 1 lemmas
- [ ] **Step 2b** — Re-prove `clauseWord_chain_consumption` using Step 1 lemmas
- [ ] **Step 3a** — Re-prove `clauseNext_good_consumption`
- [ ] **Step 3b** — Re-prove `clauseNext_bad_consumption`
- [ ] **Step 3c** — Re-prove `clauseNext_chain_consumption`
- [ ] **Step 4**  — Delete dead code; confirm clean build

### Completed prerequisites
- [x] All bundled `testWord_consumption` / `endTestWord_consumption` call sites
      replaced with individual `_actd` / `_nactd` / `_disq` variants
- [x] `start_clause_start` and `start_clause_disq` in `StartClause.lean`

