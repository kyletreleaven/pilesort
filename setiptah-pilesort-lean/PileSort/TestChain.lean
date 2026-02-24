/-
  Test chain end lemmas: combining testWord chains with endTestWord.

  These combine testChain_actd/testChain_disq (from ClauseWord) with
  endTestWord_consumption to give end-to-end results for the
  testWords ++ endTestWord portion of clauseWord.

  Generalized to start from any index j, so the same lemma covers:
  - j=0: full chain from the beginning (used by clauseWord_chain_consumption)
  - j>0: tail chain after activation (used by clauseWord_start satisfying case)
-/
import PileSort.ClauseWord

/-- From ACTD: k testWords (indices j..j+k-1) + endTestWord (j+k) reach END_POS
    when the sentinel Q is at position k+1 in A1.

    Proof:
    1. Reassociate word as testWords ++ (endTestWord ++ suffix).
    2. testChain_actd (k steps): shifts by k*m, stays ACTD on A1.drop(k) ++ A2.
    3. A1.drop(k) = [A1[k], Q] (since A1.length = k+2, A1[k+1] = Q).
    4. endTestWord_consumption ACTD case with y=Q: = m + suffix from END_POS.
    5. Total: k*m + m = (k+1)*m. -/
theorem testChain_actd_end (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ [])
    (hQ : A1[k + 1]'(by omega) = PileType.Q) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) ACTD =
    (k + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  sorry

/-- From CLAUSE_DISQ: k testWords (indices j..j+k-1) + endTestWord (j+k) reach
    penalty zone, consuming k+2 blocks total.

    Proof:
    1. Reassociate word as testWords ++ (endTestWord ++ suffix).
    2. testChain_disq (k steps): shifts by k*m, stays ≥ CLAUSE_DISQ on A1.drop(k) ++ A2.
    3. A1.drop(k) has ≥ 2 elements (since A1.length = k+2).
    4. endTestWord_consumption CLAUSE_DISQ case: ≥ 2*m + suffix from CHAIN_DISQ on A2.
    5. Total: k*m + 2*m = (k+2)*m. -/
theorem testChain_disq_end (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ []) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    (k + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  sorry
