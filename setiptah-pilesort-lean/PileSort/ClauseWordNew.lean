import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.StartClause
import PileSort.TestConsume
import PileSort.TestChain

/-- When A1 has exactly k+2 elements, dropping the first k gives the last two. -/
theorem list_drop_two {α : Type} (A1 : List α) (k : Nat) (hA1 : A1.length = k + 2) :
    A1.drop k = [A1[k]'(by omega), A1[k + 1]'(by omega)] := by
  have hdlen : (A1.drop k).length = 2 := by rw [List.length_drop, hA1]; omega
  match h : A1.drop k, hdlen with
  | [a, b], _ =>
    simp; constructor
    · have := List.getElem_drop (i := k) (j := 0) (h := by omega) A1; simp [h] at this; exact this
    · have := List.getElem_drop (i := k) (j := 1) (h := by omega) A1; simp [h] at this; exact this

theorem list_drop_append_two {α : Type} (A1 A2 : List α) (k : Nat) (hA1 : A1.length = k + 2) :
    (A1 ++ A2).drop k = A1[k]'(by omega) :: A1[k + 1]'(by omega) :: A2 := by
  rw [List.drop_append_eq_append_drop,
      show k - A1.length = 0 from by omega, List.drop_zero,
      list_drop_two A1 k hA1]; simp

theorem list_drop_append_two_last {α : Type} (A1 A2 : List α) (n : Nat)
    (hA1 : A1.length = n + 1) (hn : n ≥ 1) :
    (A1 ++ A2).drop (n - 1) = A1[n - 1]'(by omega) :: A1[n]'(by omega) :: A2 := by
  have h := list_drop_append_two A1 A2 (n - 1) (by omega)
  simp only [show n - 1 + 1 = n from by omega] at h
  exact h

/-- clauseWord in consumption form from CHAIN_DISQ: consumes n+1 blocks.

    Proof: unfold clauseWord, start_clause_disq + testChain_disq_cons + endTestWord_consumption_disq. -/
theorem clauseWord_chain_consumption (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord (clauseWord n clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CHAIN_DISQ ≥
    (n + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  unfold clauseWord
  rw [show START_CLAUSE ++ (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause ++ suffix =
      START_CLAUSE ++ ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        (endTestWord (n - 1) clause ++ suffix)) from by simp [List.append_assoc]]
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, A1 = t :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  simp only [List.cons_append]
  rw [List.range_eq_range']
  -- 1. start_clause_disq: CHAIN_DISQ → ≥ CLAUSE_DISQ on same machine
  have hsc := start_clause_disq
    ((List.range' 0 (n - 1)).flatMap (fun i => testWord i clause) ++ (endTestWord (n - 1) clause ++ suffix))
    t (rest ++ A2)
  -- 2. testChain_disq_cons: n-1 testWords, consuming (t :: rest).take (n-1)
  have hC_ne : (t :: rest).drop (n - 1) ++ A2 ≠ [] := by
    cases h : (t :: rest).drop (n - 1) with
    | nil =>
      exfalso; have := congrArg List.length h
      simp [List.length_drop, hA1] at this; omega
    | cons _ _ => simp
  have htc := testChain_disq_cons ((t :: rest).take (n - 1)) ((t :: rest).drop (n - 1) ++ A2)
    0 clause (endTestWord (n - 1) clause ++ suffix) hC_ne
  rw [show (t :: rest).take (n - 1) ++ ((t :: rest).drop (n - 1) ++ A2) = (t :: rest) ++ A2 from by
      rw [← List.append_assoc, List.take_append_drop]] at htc
  simp only [List.cons_append] at htc
  rw [show ((t :: rest).take (n - 1)).length = n - 1 from by
      rw [List.length_take]; simp [hA1]; omega] at htc
  -- 3. Rewrite (t :: rest).drop (n-1) ++ A2 to x :: y :: A2 form
  have hdrop : (t :: rest).drop (n - 1) ++ A2 =
      (t :: rest)[n - 1]'(by simp [hA1]; omega) :: (t :: rest)[n]'(by simp [hA1]) :: A2 := by
    have h : ((t :: rest) ++ A2).drop (n - 1) = (t :: rest).drop (n - 1) ++ A2 := by
      rw [List.drop_append_eq_append_drop,
          show n - 1 - (t :: rest).length = 0 from by simp [hA1]; omega, List.drop_zero]
    rw [← h]; exact list_drop_append_two_last (t :: rest) A2 n hA1 (by omega)
  rw [hdrop] at htc
  -- 4. endTestWord_consumption_disq
  have hend := endTestWord_consumption_disq (n - 1) clause suffix
    ((t :: rest)[n - 1]'(by simp [hA1]; omega)) ((t :: rest)[n]'(by simp [hA1])) A2 hA2
  -- 5. Combine
  show _ ≥ (n + 1) * ALIGN.length + _
  rw [show (n + 1) * ALIGN.length = (n - 1) * ALIGN.length + 2 * ALIGN.length from by
      rw [show n + 1 = (n - 1) + 2 from by omega, Nat.add_mul]]
  omega
