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
  -- 1. Reassociate word
  rw [show (List.range' j k).flatMap (fun i => testWord i clause) ++
        endTestWord (j + k) clause ++ suffix =
      (List.range' j k).flatMap (fun i => testWord i clause) ++
        (endTestWord (j + k) clause ++ suffix) from List.append_assoc ..]
  -- 2. Decompose A1.drop(k) = [x, Q] since A1.length = k+2 and A1[k+1] = Q
  obtain ⟨x, hdrop⟩ : ∃ x, A1.drop k = [x, PileType.Q] := by
    have hdlen : (A1.drop k).length = 2 := by rw [List.length_drop, hA1]; omega
    match h : A1.drop k, hdlen with
    | [a, b], _ =>
      have : b = PileType.Q := by
        have h1 : (A1.drop k)[1] = A1[k + 1] := List.getElem_drop A1
        simp [h] at h1; rw [h1]; exact hQ
      exact ⟨a, by rw [this]⟩
  -- 3. testChain_actd: k steps on A1 ++ A2
  have hlen : k < (A1 ++ A2).length := by simp [hA1]; omega
  have htc := testChain_actd k j clause (endTestWord (j + k) clause ++ suffix) (A1 ++ A2) hlen
  have hdrop2 : (A1 ++ A2).drop k = x :: PileType.Q :: A2 := by
    rw [List.drop_append_eq_append_drop, hdrop,
        show k - A1.length = 0 from by omega, List.drop_zero]; simp
  rw [hdrop2] at htc
  -- 4. endTestWord_consumption ACTD case with y = Q
  have hend_raw := (endTestWord_consumption (j + k) clause suffix x PileType.Q A2 hA2).2
  rw [if_pos rfl] at hend_raw
  -- 5. Combine via rw: goal becomes k*m + (m + suffix_result) = (k+1)*m + suffix_result
  rw [htc, hend_raw.1]
  show k * ALIGN.length + (ALIGN.length + _) = (k + 1) * ALIGN.length + _
  rw [show (k + 1) * ALIGN.length = k * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul], Nat.add_assoc]

/-- From CLAUSE_DISQ: k testWords (indices j..j+k-1) + endTestWord (j+k) reach
    penalty zone, consuming k+2 blocks total.

    Proof:
    1. Reassociate word as testWords ++ (endTestWord ++ suffix).
    2. testChain_disq (k steps): shifts by k*m, stays ≥ CLAUSE_DISQ on A1.drop(k) ++ A2.
    3. A1.drop(k) has ≥ 2 elements (since A1.length = k+2).
    4. endTestWord_consumption CLAUSE_DISQ case: ≥ 2*m + suffix from CHAIN_DISQ on A2.
    5. Total: k*m + 2*m = (k+2)*m. -/
theorem testChain_disq_end' (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ []) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    (k + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  -- 1. Reassociate word, apply testChain_disq, rewrite drop
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htc := testChain_disq k j clause (endTestWord (j + k) clause ++ suffix) (A1 ++ A2) (by simp [hA1]; omega)
  rw [list_drop_append_two A1 A2 k hA1] at htc
  -- 2. endTestWord_consumption CLAUSE_DISQ case
  have hend := (endTestWord_consumption (j + k) clause suffix (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2).1
  -- 3. Combine: htc ≥ k*m + hend, hend ≥ 2*m + suffix result
  show _ ≥ (k + 2) * ALIGN.length + _
  rw [show (k + 2) * ALIGN.length = k * ALIGN.length + 2 * ALIGN.length from by
    rw [Nat.add_mul]]; omega

/-- From NACTD at activation site: the activating testWord (index j, matching A1[0])
    transitions NACTD → ACTD, then k remaining testWords + endTestWord reach END_POS.

    Proof:
    1. Peel first testWord via range'_succ + flatMap_cons.
    2. testWord_consumption NACTD case with hlit: = m + rest from ACTD on A1.tail ++ A2.
    3. testChain_actd_end on tail (k steps, index j+1): = (k+1)*m + suffix from END_POS.
    4. Total: m + (k+1)*m = (k+2)*m. -/
theorem testChain_activate_end (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 3) (hA2 : A2 ≠ [])
    (hQ : A1[k + 2]'(by omega) = PileType.Q)
    (hlit : matchesLiteral (A1[0]'(by omega)) j clause) :
    applyWord ((List.range' j (k + 1)).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k + 1) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    (k + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  -- 1. Peel off the activating testWord
  obtain ⟨a, rest, rfl⟩ : ∃ a rest, A1 = a :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  simp only [List.getElem_cons_zero] at hlit
  rw [show (List.range' j (k + 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (j + k + 1) clause ++ suffix =
      testWord j clause ++ ((List.range' (j + 1) k).flatMap (fun i => testWord i clause) ++
        endTestWord (j + k + 1) clause ++ suffix) from by
    rw [List.range'_succ, List.flatMap_cons]; simp [List.append_assoc]]
  -- Normalize (a :: rest) ++ A2 to a :: (rest ++ A2)
  simp only [List.cons_append]
  -- 2. testWord_consumption NACTD case with matching literal → ACTD
  have hrest_ne : rest ++ A2 ≠ [] := by
    have : rest.length = k + 2 := by simp at hA1; omega
    simp [show rest ≠ [] from by intro h; simp [h] at this]
  have htw := (testWord_consumption j clause
    ((List.range' (j + 1) k).flatMap (fun i => testWord i clause) ++
      endTestWord (j + k + 1) clause ++ suffix)
    a (rest ++ A2) hrest_ne).2.2
  rw [if_pos hlit] at htw
  rw [htw]
  -- 3. testChain_actd_end on tail
  have hrest_len : rest.length = k + 2 := by simp at hA1; omega
  have hQ' : rest[k + 1]'(by omega) = PileType.Q := by
    have : (a :: rest)[k + 2]'(by omega) = PileType.Q := hQ
    simpa using this
  have hae := testChain_actd_end k (j + 1) clause suffix rest A2 hrest_len hA2 hQ'
  rw [show j + 1 + k = j + k + 1 from by omega] at hae
  rw [hae]
  -- 4. Arithmetic: m + (k+1)*m = (k+2)*m
  rw [show (k + 2) * ALIGN.length = ALIGN.length + (k + 1) * ALIGN.length from by
    rw [show k + 2 = 1 + (k + 1) from by omega, Nat.add_mul, Nat.one_mul]]
  omega
