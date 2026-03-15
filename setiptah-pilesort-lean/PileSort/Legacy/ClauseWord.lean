
import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.StartClause
import PileSort.TestConsume
import PileSort.TestChain
import PileSort.ClauseWord


/-- From ACTD: k testWords (indices j..j+k-1) + endTestWord (j+k) reach END_POS
    when the sentinel Q is at position k+1 in A1 (old form). -/
theorem testChain_actd_end (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ [])
    (hQ : A1[k + 1]'(by omega) = PileType.Q) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) ACTD =
    (k + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  -- 1. Reassociate word, apply testChain_actd, rewrite drop
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htc := testChain_actd k j clause (endTestWord (j + k) clause ++ suffix) (A1 ++ A2) (by simp [hA1]; omega)
  rw [list_drop_append_two A1 A2 k hA1] at htc
  -- 2. endTestWord_consumption_actd with y = Q
  have hend_raw := endTestWord_consumption_actd (j + k) clause suffix (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2
  rw [hQ, if_pos rfl] at hend_raw
  -- 3. Combine via rw
  rw [htc, show A1[k + 1] = PileType.Q from hQ, hend_raw]
  show k * ALIGN.length + (ALIGN.length + _) = (k + 1) * ALIGN.length + _
  rw [show (k + 1) * ALIGN.length = k * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul], Nat.add_assoc]

/-- From NACTD at activation site (old form): the activating testWord (index j, matching A1[0])
    transitions NACTD → ACTD, then k remaining testWords + endTestWord reach END_POS. -/
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
  -- 2. testWord_consumption_nactd with matching literal → ACTD
  have hrest_ne : rest ++ A2 ≠ [] := by
    have : rest.length = k + 2 := by simp at hA1; omega
    simp [show rest ≠ [] from by intro h; simp [h] at this]
  have htw := testWord_consumption_nactd j clause
    ((List.range' (j + 1) k).flatMap (fun i => testWord i clause) ++
      endTestWord (j + k + 1) clause ++ suffix)
    a (rest ++ A2) hrest_ne
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

/-- NACTD with no matching literals in A1: stays at exactly NACTD after shifting
    past A1. Consumption form: A1 is consumed, A2 remains. -/
theorem testChain_nactd : ∀ (A1 A2 : List PileType)
    (start : Nat) (clause : Clause) (suffix : List Action), A2 ≠ [] →
    (∀ i (hi : i < A1.length), ¬matchesLiteral A1[i] (start + i) clause) →
    applyWord ((List.range' start A1.length).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    A1.length * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) NACTD
  | [], _, _, _, _, _, _ => by simp
  | a :: rest, A2, start, clause, suffix, hA2, hno => by
    show applyWord ((List.range' start (rest.length + 1)).flatMap _ ++ suffix) _ _ = _
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have hno0 : ¬matchesLiteral a start clause := by
      simpa using hno 0 (by simp)
    have hrest_ne : rest ++ A2 ≠ [] := by simp [show rest ++ A2 ≠ [] from by
      cases rest <;> simp [hA2]]
    have htw := testWord_consumption_nactd start clause
      ((List.range' (start + 1) rest.length).flatMap (fun i => testWord i clause) ++ suffix)
      a (rest ++ A2) hrest_ne
    rw [if_neg hno0] at htw
    have hih := testChain_nactd rest A2 (start + 1) clause suffix hA2 (by
      intro i hi
      have := hno (i + 1) (by simp; omega)
      simp only [List.getElem_cons_succ] at this
      rw [show start + (i + 1) = start + 1 + i from by omega] at this
      exact this)
    simp only [List.cons_append] at htw ⊢
    rw [htw, hih]
    show ALIGN.length + (rest.length * ALIGN.length + _) =
      (rest.length + 1) * ALIGN.length + _
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- Adapter: testChain_nactd for A1 ++ A2 with hno on A1[i]. -/
theorem testChain_nactd_split (k start : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hlen : k < A1.length)
    (hno : ∀ i (hi : i < k), ¬matchesLiteral (A1[i]'(by omega)) (start + i) clause) :
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (A1.drop k ++ A2))) NACTD := by
  have h := testChain_nactd_old k start clause suffix (A1 ++ A2) (by simp; omega)
    (by intro i hi; rw [List.getElem_append_left (by omega)]; exact hno i hi)
  rw [List.drop_append_eq_append_drop,
      show k - A1.length = 0 from by omega, List.drop_zero] at h
  exact h

/-- Adapter: testChain_activate_end for A1 with activation at offset i₀.
    Wraps testChain_activate_end on A1.drop i₀, proving getElem_drop facts internally. -/
theorem testChain_activate_end_split (k j i₀ : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = i₀ + k + 3) (hA2 : A2 ≠ [])
    (hQ : A1[i₀ + k + 2]'(by omega) = PileType.Q)
    (hlit : matchesLiteral (A1[i₀]'(by omega)) j clause) :
    applyWord ((List.range' j (k + 1)).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k + 1) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1.drop i₀ ++ A2))) NACTD =
    (k + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  have hdrop_len : (A1.drop i₀).length = k + 3 := by
    rw [List.length_drop]; omega
  have hQ' : (A1.drop i₀)[k + 2]'(by omega) = PileType.Q := by
    simp only [List.getElem_drop, show i₀ + (k + 2) = i₀ + k + 2 from by omega]; exact hQ
  have hlit' : matchesLiteral ((A1.drop i₀)[0]'(by omega)) j clause := by
    simp only [List.getElem_drop, Nat.add_zero]; exact hlit
  exact testChain_activate_end k j clause suffix (A1.drop i₀) A2 hdrop_len hA2 hQ' hlit'

/-- From NACTD with no matching literals anywhere: k testWords (indices j..j+k-1) +
    endTestWord (j+k) all fail to activate, reaching penalty zone.
    Requires y = Q (the sentinel) and ¬matchesLiteral for the endTestWord too.

    Proof:
    1. Reassociate word, apply testChain_nactd, rewrite drop via list_drop_append_two.
    2. endTestWord_consumption NACTD case with y=Q, ¬matchesLiteral: ≥ nextBad.
    3. Arithmetic: k*m + 2*m = (k+2)*m. -/
theorem testChain_nactd_end_old (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ [])
    (hQ : A1[k + 1]'(by omega) = PileType.Q)
    (hno : ∀ i (hi : i < k), ¬matchesLiteral (A1[i]'(by omega)) (j + i) clause)
    (hno_end : ¬matchesLiteral (A1[k]'(by omega)) (j + k) clause) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD ≥
    (k + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  -- 1. Reassociate word, apply testChain_nactd, rewrite drop
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htc := testChain_nactd_old k j clause (endTestWord (j + k) clause ++ suffix) (A1 ++ A2) (by simp [hA1]; omega) (by
    intro i hi
    rw [List.getElem_append_left (by omega)]
    exact hno i hi)
  rw [list_drop_append_two A1 A2 k hA1, show A1[k + 1] = PileType.Q from hQ] at htc
  -- 2. endTestWord_consumption_nactd with y=Q, ¬matchesLiteral
  have hend_raw := endTestWord_consumption_nactd (j + k) clause suffix (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2
  rw [hQ, if_neg (by simp [hno_end])] at hend_raw
  -- 3. Combine
  show _ ≥ (k + 2) * ALIGN.length + _
  rw [show (k + 2) * ALIGN.length = k * ALIGN.length + 2 * ALIGN.length from by
    rw [Nat.add_mul]]; omega

/-- From NACTD with no matching literals anywhere, sentinel decomposition form.
    A1 = non-matching variables, x = last variable (non-matching for endTestWord),
    Q = sentinel, A2 = rest of machine. -/
theorem testChain_nactd_end (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (hno : ∀ i (hi : i < A1.length), ¬matchesLiteral (A1[i]) (j + i) clause)
    (hno_end : ¬matchesLiteral x (j + A1.length) clause) :
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: PileType.Q :: A2))) NACTD ≥
    (A1.length + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  -- 1. Reassociate word, apply testChain_nactd
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htc := testChain_nactd A1 (x :: PileType.Q :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp) hno
  rw [htc]
  -- 2. endTestWord_consumption_nactd with y=Q, ¬matchesLiteral
  have hend := endTestWord_consumption_nactd (j + A1.length) clause suffix x PileType.Q A2 hA2
  rw [if_neg (by simp [hno_end])] at hend
  -- 3. Combine
  rw [show (A1.length + 2) * ALIGN.length = A1.length * ALIGN.length + 2 * ALIGN.length from by
    rw [Nat.add_mul]]; omega

/-- Case i₀ < k: activation during a regular testWord.
    Proof sketch:
    1. Split range [j..j+k) into [j..j+i₀) ++ [j+i₀..j+k).
    2. testChain_nactd_split on prefix (i₀ steps, stays NACTD) on A1 ++ A2.
    3. list_drop_two + List.cons_append to rewrite A1.drop i₀ ++ A2 for activate_end.
    4. testChain_activate_end on tail (k-i₀ steps from NACTD, activates at A1[i₀]).
    5. Arithmetic: i₀ * m + (k-1-i₀+2) * m = (k+1) * m. -/
theorem testChain_sat_end_lt (k j i₀ : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ [])
    (hQ : A1[k + 1]'(by omega) = PileType.Q)
    (hi₀ : i₀ < k)
    (hml : matchesLiteral (A1[i₀]'(by omega)) (j + i₀) clause)
    (hno : ∀ i (hi : i < i₀), ¬matchesLiteral (A1[i]'(by omega)) (j + i) clause) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    (k + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  -- 1. Reassociate word, split range
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from
    List.append_assoc ..]
  have hrange : List.range' j k = List.range' j i₀ ++ List.range' (j + i₀) (k - i₀) := by
    have := List.range'_append j i₀ (k - i₀) 1
    simp only [Nat.one_mul] at this
    rw [show k - i₀ + i₀ = k from by omega] at this
    exact this.symm
  rw [hrange, List.flatMap_append, List.append_assoc]
  -- 2. testChain_nactd_split on prefix
  have htcn := testChain_nactd_split i₀ j clause
    ((List.range' (j + i₀) (k - i₀)).flatMap (fun i => testWord i clause) ++
      (endTestWord (j + k) clause ++ suffix))
    A1 A2 (by omega) hno
  rw [htcn]
  -- 3. Reassociate for testChain_activate_end_split, then apply
  rw [show k - i₀ = (k - 1 - i₀) + 1 from by omega,
      show j + k = j + i₀ + (k - 1 - i₀) + 1 from by omega,
      ← List.append_assoc]
  have htae := testChain_activate_end_split (k - 1 - i₀) (j + i₀) i₀ clause suffix
    A1 A2 (by omega) hA2
    (by simp only [show i₀ + (k - 1 - i₀) + 2 = k + 1 from by omega]; exact hQ)
    hml
  rw [htae]
  -- 4. Arithmetic: i₀ * m + (k-1-i₀+2) * m = (k+1) * m
  rw [← Nat.add_assoc, ← Nat.add_mul,
      show i₀ + (k - 1 - i₀ + 2) = k + 1 from by omega]

/-- Case i₀ = k: activation at the endTestWord (old form). -/
theorem testChain_sat_end_eq_old (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ [])
    (hQ : A1[k + 1]'(by omega) = PileType.Q)
    (hml : matchesLiteral (A1[k]'(by omega)) (j + k) clause)
    (hno : ∀ i (hi : i < k), ¬matchesLiteral (A1[i]'(by omega)) (j + i) clause) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    (k + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  -- 1. Reassociate word, apply testChain_nactd_split
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from
    List.append_assoc ..]
  have htcn := testChain_nactd_split k j clause (endTestWord (j + k) clause ++ suffix)
    A1 A2 (by omega) hno
  rw [htcn]
  -- 2. Rewrite A1.drop k as [A1[k], A1[k+1]], then A1[k+1] → Q, normalize list append
  rw [list_drop_two A1 k hA1, show A1[k + 1] = PileType.Q from hQ]
  simp only [List.cons_append, List.nil_append]
  -- 3. endTestWord_consumption_nactd with matchesLiteral and y=Q
  have hend := endTestWord_consumption_nactd (j + k) clause suffix
    (A1[k]'(by omega)) PileType.Q A2 hA2
  rw [if_pos ⟨rfl, hml⟩] at hend
  rw [hend]
  -- 4. Arithmetic: k * m + m = (k+1) * m
  rw [show (k + 1) * ALIGN.length = k * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul]]
  omega

/-- Combined: dispatches on i₀ < k vs i₀ = k. -/
theorem testChain_sat_end (k j i₀ : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ [])
    (hQ : A1[k + 1]'(by omega) = PileType.Q)
    (hi₀ : i₀ ≤ k)
    (hml : matchesLiteral (A1[i₀]'(by omega)) (j + i₀) clause)
    (hno : ∀ i (hi : i < i₀), ¬matchesLiteral (A1[i]'(by omega)) (j + i) clause) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    (k + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  rcases Nat.lt_or_eq_of_le hi₀ with hi₀' | rfl
  · exact testChain_sat_end_lt k j i₀ clause suffix A1 A2 hA1 hA2 hQ hi₀' hml hno
  · exact testChain_sat_end_eq_old i₀ j clause suffix A1 A2 hA1 hA2 hQ hml hno

/-- Specialization of testChain_sat_end with j=0: uses List.range and plain indices. -/
theorem testChain_sat_end_zero (k i₀ : Nat) (clause : Clause)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ [])
    (hQ : A1[k + 1]'(by omega) = PileType.Q)
    (hi₀ : i₀ ≤ k)
    (hml : matchesLiteral (A1[i₀]'(by omega)) i₀ clause)
    (hno : ∀ i (hi : i < i₀), ¬matchesLiteral (A1[i]'(by omega)) i clause) :
    applyWord ((List.range k).flatMap (fun i => testWord i clause) ++
              endTestWord k clause)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD =
    (k + 1) * ALIGN.length +
      applyWord [] (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  have h := testChain_sat_end k 0 i₀ clause [] A1 A2 hA1 hA2 hQ hi₀
    (by simp; exact hml) (by intro i hi; simp; exact hno i hi)
  simp only [List.range_eq_range', List.append_nil, Nat.zero_add] at h ⊢
  exact h
