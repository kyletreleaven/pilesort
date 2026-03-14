/-
  TestChain: consumption-form lemmas for a sequence of testWords.

  ## Representation choice: A1 ++ A2 vs types.drop k

  The individual `testWord_consumption_*` lemmas in TestConsume use `x :: rest`
  to describe the pile-type list: one word consumes `x` from the front and
  leaves `rest` for the suffix. This is natural for a single step.

  When chaining k test words, there are two equivalent ways to parameterize
  the pile-type list:

  **Index form** (`types` + `k < types.length`, result mentions `types.drop k`):
    Used by the old `testChain_disq` in ClauseWordCorrect.lean.  Falls out
    naturally from naïve induction — each step increments k and peels one
    element — but `types.drop k` is opaque at call sites and requires extra
    rewrites to unfold.

  **Destructured form** (`A1 ++ A2`, result mentions `A2` directly):
    Used by all three lemmas in this file.  The caller pre-splits the list at
    the boundary and names both halves; the conclusion then mentions `A2`
    directly, with no `drop` expression to simplify away.  The guard condition
    `A2 ≠ []` replaces `k < types.length`.

  The two forms are logically equivalent (set `A1 = types.take k`,
  `A2 = types.drop k`), but the destructured form is more ergonomic: call
  sites already have concrete `A1`/`A2` in hand, and no extra simp lemmas
  about `List.drop` are needed to connect the conclusion to the rest of the
  proof.
-/
import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.StartClause
import PileSort.TestConsume

open Classical

/-- ACTD in consumption form: from ACTD, testWords shift past A1 and stay ACTD. -/
theorem testChain_actd_cons : ∀ (A1 A2 : List PileType)
    (start : Nat) (clause : Clause) (suffix : List Action), A2 ≠ [] →
    applyWord ((List.range' start A1.length).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) ACTD =
    A1.length * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) ACTD
  | [], _, _, _, _, _ => by simp
  | a :: rest, A2, start, clause, suffix, hA2 => by
    show applyWord ((List.range' start (rest.length + 1)).flatMap _ ++ suffix) _ _ = _
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have hrest_ne : rest ++ A2 ≠ [] := by
      cases rest <;> simp [hA2]
    have htw := testWord_consumption_actd start clause
      ((List.range' (start + 1) rest.length).flatMap (fun i => testWord i clause) ++ suffix)
      a (rest ++ A2) hrest_ne
    have hih := testChain_actd_cons rest A2 (start + 1) clause suffix hA2
    simp only [List.cons_append] at htw ⊢
    rw [htw, hih]
    show ALIGN.length + (rest.length * ALIGN.length + _) =
      (rest.length + 1) * ALIGN.length + _
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- CLAUSE_DISQ in consumption form: from CLAUSE_DISQ, testWords shift past A1
    with ≥ CLAUSE_DISQ at each step. -/
theorem testChain_disq_cons : ∀ (A1 A2 : List PileType)
    (start : Nat) (clause : Clause) (suffix : List Action), A2 ≠ [] →
    applyWord ((List.range' start A1.length).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    A1.length * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CLAUSE_DISQ
  | [], _, _, _, _, _ => by simp
  | a :: rest, A2, start, clause, suffix, hA2 => by
    show applyWord ((List.range' start (rest.length + 1)).flatMap _ ++ suffix) _ _ ≥ _
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have hrest_ne : rest ++ A2 ≠ [] := by
      cases rest <;> simp [hA2]
    have htw := testWord_consumption_disq start clause
      ((List.range' (start + 1) rest.length).flatMap (fun i => testWord i clause) ++ suffix)
      a (rest ++ A2) hrest_ne
    have hih := testChain_disq_cons rest A2 (start + 1) clause suffix hA2
    simp only [List.cons_append] at htw ⊢
    show _ ≥ (rest.length + 1) * ALIGN.length + _
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- NACTD combined: from NACTD, testWords shift past A1, landing at ACTD if some A1[i]
    matches, NACTD otherwise. -/
theorem testChain_nactd_cons : ∀ (A1 A2 : List PileType)
    (start : Nat) (clause : Clause) (suffix : List Action), A2 ≠ [] →
    applyWord ((List.range' start A1.length).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    A1.length * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2))
        (if ∃ i : Fin A1.length, matchesLiteral A1[i] (start + ↑i) clause then ACTD else NACTD)
  | [], _, _, _, _, _ => by
    rw [if_neg (fun ⟨i, _⟩ => i.elim0)]
    simp
  | a :: rest, A2, start, clause, suffix, hA2 => by
    show applyWord ((List.range' start (rest.length + 1)).flatMap _ ++ suffix) _ _ = _
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have hrest_ne : rest ++ A2 ≠ [] := by cases rest <;> simp [hA2]
    have htw := testWord_consumption_nactd start clause
      ((List.range' (start + 1) rest.length).flatMap (fun i => testWord i clause) ++ suffix)
      a (rest ++ A2) hrest_ne
    simp only [List.cons_append] at htw ⊢
    rcases Classical.em (matchesLiteral a start clause) with hlit | hlit
    · -- head activates: NACTD → ACTD, tail stays ACTD via testChain_actd_cons
      rw [if_pos hlit] at htw
      rw [htw, testChain_actd_cons rest A2 (start + 1) clause suffix hA2]
      have hex : ∃ i : Fin (a :: rest).length, matchesLiteral (a :: rest)[i] (start + ↑i) clause :=
        ⟨⟨0, by simp⟩, by simp [hlit]⟩
      rw [if_pos hex]
      simp only [List.length_cons]
      show ALIGN.length + (rest.length * ALIGN.length + _) = (rest.length + 1) * ALIGN.length + _
      rw [Nat.add_mul, Nat.one_mul]; omega
    · -- head doesn't activate: stays NACTD, existential collapses to tail
      rw [if_neg hlit] at htw
      rw [htw, testChain_nactd_cons rest A2 (start + 1) clause suffix hA2]
      have heq : (∃ i : Fin (rest.length + 1), matchesLiteral (a :: rest)[i] (start + ↑i) clause) ↔
                 (∃ i : Fin rest.length, matchesLiteral rest[i] (start + 1 + ↑i) clause) := by
        constructor
        · rintro ⟨⟨i, hi⟩, hm⟩
          cases i with
          | zero => simp only [List.getElem_cons_zero, Nat.add_zero] at hm; exact absurd hm hlit
          | succ j =>
            exact ⟨⟨j, by simp at hi; omega⟩, by
              simp only [List.getElem_cons_succ] at hm
              rwa [show start + (j + 1) = start + 1 + j from by omega] at hm⟩
        · rintro ⟨⟨j, hj⟩, hm⟩
          refine ⟨⟨j + 1, by omega⟩, ?_⟩
          simp only [List.getElem_cons_succ]
          rwa [show start + (j + 1) = start + 1 + j from by omega]
      simp only [List.length_cons, heq]
      show ALIGN.length + (rest.length * ALIGN.length + _) = (rest.length + 1) * ALIGN.length + _
      rw [Nat.add_mul, Nat.one_mul]; omega

/-- Chaining testWords from CLAUSE_DISQ: each step shifts by one block and preserves ≥ CLAUSE_DISQ.
    After k steps on range' start k, the result is ≥ k * m + (suffix result on dropped types).

    Induction on k:
    - k = 0: range' is empty, trivial.
    - k + 1: peel off testWord start via range'_succ + flatMap_cons.
      testWord_consumption (CLAUSE_DISQ case) gives ≥ m + (rest on tail).
      IH gives rest on tail ≥ k * m + (suffix on drop). Combine with omega. -/
theorem testChain_disq : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType), k < types.length →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) CLAUSE_DISQ >=
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) CLAUSE_DISQ
  | 0, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have htw := testWord_consumption_disq start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest
    have hih := testChain_disq k (start + 1) clause suffix rest (by omega)
    show _ >= (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) CLAUSE_DISQ
    rw [Nat.succ_mul]; omega

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
  -- 2. endTestWord_consumption_disq
  have hend := endTestWord_consumption_disq (j + k) clause suffix (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2
  -- 3. Combine: htc ≥ k*m + hend, hend ≥ 2*m + suffix result
  show _ ≥ (k + 2) * ALIGN.length + _
  rw [show (k + 2) * ALIGN.length = k * ALIGN.length + 2 * ALIGN.length from by
    rw [Nat.add_mul]]; omega
