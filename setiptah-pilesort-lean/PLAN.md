# Plan

## Cleanup: remove old FormulaWord machinery

Most of this has already been deleted. Remaining items still in the codebase:

- `next_correct_rep` in `FormulaWord.lean`
- `virtualPileTypes_replicate_Q_cons'` (and variant) in `FormulaWord.lean`
- `formulaState` definition in `Reduction.lean`

`not_satisfiesFormula_rest` must stay (used in `formulaWord_unsat_pos'`).

## TestChain.lean (done)

`TestChain.lean` holds consumption-form lemmas for `testWord` sequences.
All three plain-chain lemmas are complete:

- `testChain_actd_cons`: from ACTD, shifts past A1, stays ACTD (= form)
- `testChain_disq_cons`: from CLAUSE\_DISQ, shifts past A1, stays ≥ CLAUSE\_DISQ
- `testChain_nactd_cons`: from NACTD, shifts past A1, lands at ACTD or NACTD
  depending on `∃ i : Fin A1.length, matchesLiteral A1[i] (start+i) clause`

End-capped lemmas (`testWords ++ endTestWord`) also in `TestChain.lean`:

- `testChain_disq_end'`: from CLAUSE\_DISQ, k testWords + endTestWord → ≥ CHAIN\_DISQ
- `testChain_actd_end_new`: from ACTD, Q sentinel hardcoded → = END\_POS
- `testChain_actd_end_disq`: from ACTD, `et ≠ Q` → ≥ CHAIN\_DISQ

End-capped lemmas (`testWords ++ endTestWord`) also in `TestChain.lean` (all done):

- `testChain_disq_end'` (from CLAUSE_DISQ → ≥ CHAIN_DISQ, A1.length = k+2 form)
- `testChain_actd_end_new` (from ACTD, Q sentinel hardcoded → = END_POS)
- `testChain_actd_end_disq` (from ACTD, non-Q sentinel `et ≠ Q` → ≥ CHAIN_DISQ)
- `testChain_nactd_end_endpos` (from NACTD, Q sentinel + any activation → = END_POS)
- `testChain_nactd_end_disq_nomatch` (from NACTD, Q sentinel + no match → ≥ CHAIN_DISQ)
- `testChain_nactd_end_disq_noQ` (from NACTD, non-Q sentinel → ≥ CHAIN_DISQ)
- `testChain_nactd_end_disq` (trivially combines the two NACTD disq cases)

### NACTD end-capped: 4 lemmas (2/3 compromise)

We considered two approaches:

- **3 lemmas**: one focused lemma per outcome sub-case, each with a clean single
  hypothesis.  Maps 1-1 onto the branches of `clauseWord_start_nonsat_cons` (Q
  case, S case) and `clauseWord_start_sat_cons`, but leaves an internal Q/S split
  in the clauseWord nonsat proof.

- **2 lemmas**: combine the two disq cases into one, absorbing the Q/S split
  internally.  Gives a cleaner clauseWord nonsat proof (no case split needed), but
  makes the combined disq lemma internally more complex.

The right choice depends on whether the combined disq proof is unwieldy — which
we don't know until we try.  Rather than commit, we provide all three focused
lemmas *plus* a trivial combined one:

- `testChain_nactd_end_endpos`: Q sentinel + any activation → = END_POS
- `testChain_nactd_end_disq_nomatch`: Q sentinel + no match anywhere → ≥ CHAIN_DISQ
- `testChain_nactd_end_disq_noQ`: non-Q sentinel → ≥ CHAIN_DISQ
- `testChain_nactd_end_disq`: trivially delegates to the two disq lemmas above

This way the focused lemmas exist regardless, and `testChain_nactd_end_disq` is
cheap to add (two-line proof).  Call sites can use whichever form fits best, and
we get empirical evidence for the 2- vs 3-lemma question without any throwaway work.

## Step 2: clauseWord consumption-form lemmas

Prove two clauseWord consumption-form lemmas in `ClauseWordNew.lean` using only
`start_clause_*` and end-capped TestChain lemmas.  The `endTestWord_consumption_*`
lemmas are no longer needed at this level — the end-capped TestChain lemmas wrap
them up.  There is no combined `clauseWord_start_consumption`; `FormulaWordNew.lean`
calls the sat/nonsat variants directly.

### Prerequisites (already exist)

`start_clause_start` and `start_clause_disq` in `StartClause.lean` are the
single-origin consumption-form lemmas for the START_CLAUSE gadget — proved via
`gadget_lift_*` + `decide`. No changes needed there.

### clauseWord from START_POS, sat case (`clauseWord_start_sat_cons`) — done

Proof structure:
1. `clauseWord_start_preamble_cons` → reduce to testWords ++ endTestWord from NACTD
2. `hasMatchingAssignment_activation` (adapter) → reshape `HasMatchingAssignment` evidence
   into the `Fin`-indexed form that `testChain_nactd_end_endpos` expects
3. `testChain_nactd_end_endpos` → = END_POS

`hasMatchingAssignment_activation` wraps `hasMatchingAssignment_some_matchesLiteral`
(which has the natural signature `∃ i : Fin n, matchesLiteral A1[i] i clause`) and
converts its output to the `Fin (A1.take (n-1)).length`-indexed / `0 + ↑i`-offset form.
This is the first concrete instance of the representation-mismatch bridge; both lemmas
live in `ClauseWordNew.lean`.

### clauseWord from START_POS, nonsat case (`clauseWord_start_nonsat_cons`) — done

Proof structure:
1. `clauseWord_start_preamble_cons` → reduce to testWords ++ endTestWord from NACTD
2. Case split on sentinel (Q or S):
   - Q: `testChain_nactd_end_disq_nomatch` → ≥ CHAIN_DISQ
   - S: `testChain_nactd_end_disq_noQ` → ≥ CHAIN_DISQ

Note: the current proof calls `endTestWord_consumption_*` directly and can be
simplified to use `testChain_nactd_end_disq_nomatch` / `testChain_nactd_end_disq_noQ`.

### clauseWord from CHAIN_DISQ (`clauseWord_chain_consumption`) — done

Proof structure:
1. `start_clause_disq` → suffix sees machine from ≥ CLAUSE_DISQ
2. `testChain_disq_end'` → ≥ CHAIN_DISQ

Note: `applyWord_mono` bridges the `≥ CLAUSE_DISQ` output of `start_clause_disq`
into `testChain_disq_end'` — same pattern as the current proof.

## Step 3: clauseNext consumption-form lemmas

Re-prove (or prove anew) the three `clauseNext` consumption-form lemmas in
`FormulaWordNew.lean` using only the clauseWord consumption lemmas from Step 2.
The target lemmas are:

- `clauseNext_good_consumption` (from START_POS)
- `clauseNext_bad_consumption` (from START_POS, unsatisfied clause)
- `clauseNext_chain_consumption` (from CHAIN_DISQ)

Each should reduce to a single `clauseWord_start_consumption` or
`clauseWord_chain_consumption` application (from Step 2), plus arithmetic.

## Representation mismatch (future work)

The `HasMatchingAssignment` / `embedVars` layer and the `matchesLiteral` layer on raw
pile types speak different languages.  Bridging them is currently done ad hoc in each
proof (e.g. `not_hasMatchingAssignment_no_matchesLiteral` for the negative direction,
`hasMatchingAssignment_some_matchesLiteral` for the positive direction).

In the longer term, consider whether `testChain_nactd_end_endpos` (and friends) should
accept `satisfiesClause`/`HasMatchingAssignment` hypotheses directly, or whether a small
library of bridge lemmas is the right abstraction.  Reducing this mismatch would shorten
the clauseWord proofs and make the proof stack easier to read top-to-bottom.

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

- [x] **Step 1a** — `testChain_actd_cons` in `TestChain.lean`
- [x] **Step 1b** — `testChain_disq_cons` (A1++A2 form) in `TestChain.lean`
- [x] **Step 1c** — `testChain_nactd_cons` in `TestChain.lean`
- [x] **Step 1d** — End-capped lemmas in `TestChain.lean`:
  - [x] `testChain_disq_end'` (migrated + reproved from `testChain_disq_cons`)
  - [x] `testChain_actd_end_new` (migrated from `ClauseWord.lean`)
  - [x] `testChain_actd_end_disq` (new)
  - [x] `testChain_nactd_end_endpos` (NACTD → END\_POS)
  - [x] `testChain_nactd_end_disq` (NACTD → ≥ CHAIN\_DISQ; see plan above)
- [x] **Step 2a** — Prove `clauseWord_start_sat_cons` in `ClauseWordNew.lean`
  - [x] `clauseWord_start_nonsat_cons` (done; simplification to TestChain lemmas deferred)
  - [x] `clauseWord_start_sat_cons`
- [x] **Step 2b** — `clauseWord_chain_consumption` (in `ClauseWordNew.lean`)
- [ ] **Step 3a** — Re-prove `clauseNext_good_consumption`
- [ ] **Step 3b** — Re-prove `clauseNext_bad_consumption`
- [ ] **Step 3c** — Re-prove `clauseNext_chain_consumption`
- [ ] **Step 4**  — Delete dead code; confirm clean build

### Dead code (pending Step 4 deletion)
In `TestChain.lean`: `testChain_activate_end_new` (subsumed by `testChain_nactd_end_endpos`)
In `ClauseWordCorrect.lean`: `testChain_disq`, `testChain_disq_end`
In `ClauseWord.lean`: `testChain_actd`, `testChain_actd_end`, `testChain_activate_end_new`,
  `testChain_activate_end`, `testChain_nactd_old`, `testChain_nactd`, `testChain_nactd_split`,
  `testChain_activate_end_split`, `testChain_nactd_end_old`, `testChain_nactd_end`,
  `testChain_sat_end_lt`, `testChain_sat_end_eq`, `testChain_sat_end_eq_old`,
  `testChain_sat_end`, `testChain_sat_end_zero`
  (verify each before deleting)

### Completed prerequisites
- [x] All bundled `testWord_consumption` / `endTestWord_consumption` call sites
      replaced with individual `_actd` / `_nactd` / `_disq` variants
- [x] `start_clause_start` and `start_clause_disq` in `StartClause.lean`

