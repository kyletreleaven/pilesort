/-
  Test chain lemmas: combining testWord chains with endTestWord.

  These combine testChain_actd/testChain_disq (from ClauseWord) with
  endTestWord_consumption to give end-to-end results for the
  testWords ++ endTestWord portion of clauseWord.
-/
import PileSort.ClauseWord

/-- From ACTD with last element of A1 = Q: testWords + endTestWord reach
    END_POS in the Q block (the sentinel), shifted by n blocks.

    Proof:
    1. Reassociate word as testWords ++ (endTestWord ++ suffix).
    2. testChain_actd (n-1 steps): shifts by (n-1)*m, stays ACTD.
    3. Decompose (A1++A2).drop(n-1) = [A1[n-1], Q] ++ A2.
    4. endTestWord_consumption ACTD case with y=Q: = m + suffix from END_POS.
    5. Total: (n-1)*m + m = n*m. -/
theorem testChain_actd_end (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ [])
    (hQ : A1[n]'(by omega) = PileType.Q) :
    applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
              endTestWord (n - 1) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) ACTD =
    n * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  sorry
