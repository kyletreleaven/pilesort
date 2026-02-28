
import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.StartClause
import PileSort.TestConsume

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

theorem list_split_last {α : Type} : ∀ (l : List α), l ≠ [] →
    ∃ init last, l = init ++ [last] ∧ init.length + 1 = l.length
  | [x], _ => ⟨[], x, rfl, rfl⟩
  | x :: y :: rest, _ => by
    have ⟨init, last, h, hlen⟩ := list_split_last (y :: rest) (by simp)
    exact ⟨x :: init, last, by rw [h]; simp, by simp_all [List.length_cons]⟩

theorem list_drop_append_two_last {α : Type} (A1 A2 : List α) (n : Nat)
    (hA1 : A1.length = n + 1) (hn : n ≥ 1) :
    (A1 ++ A2).drop (n - 1) = A1[n - 1]'(by omega) :: A1[n]'(by omega) :: A2 := by
  have h := list_drop_append_two A1 A2 (n - 1) (by omega)
  simp only [show n - 1 + 1 = n from by omega] at h
  exact h

/-- There exists a Boolean assignment of length n whose embedding matches xs
    and that satisfies predicate P (typically satisfiesClause or satisfiesFormula). -/
def HasMatchingAssignment (n : Nat) (xs : List PileType) (P : List Bool → Prop) : Prop :=
  ∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q] ∧ P vars

/-- matchesLiteral on an embedded Bool reduces to the literal satisfaction condition. -/
theorem matchesLiteral_embedVar (b : Bool) (i : Nat) (clause : Clause) :
    matchesLiteral (embedVar b) i clause ↔
      (clause.getD i .absent = .pos ∧ b = true) ∨ (clause.getD i .absent = .neg ∧ b = false) := by
  cases b <;> simp [matchesLiteral, litMatches, embedVar]

/-- satisfiesClause is equivalent to matchesLiteral firing at some in-range variable index. -/
theorem satisfiesClause_iff_matchesLiteral (vars : List Bool) (clause : Clause) :
    satisfiesClause vars clause ↔
      ∃ i, i < vars.length ∧ matchesLiteral (embedVar (vars.getD i false)) i clause := by
  simp only [satisfiesClause, matchesLiteral_embedVar]

/-- ACTD is a trap: from ACTD, testWords stay at exactly ACTD after shifting.
    Mirrors testChain_disq but uses the ACTD equality case. -/
theorem testChain_actd : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType), k < types.length →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) ACTD =
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) ACTD
  | 0, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have htw := (testWord_consumption start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest).1
    have hih := testChain_actd k (start + 1) clause suffix rest (by omega)
    show _ = (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) ACTD
    rw [Nat.succ_mul, htw, hih]; omega

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
    have htw := (testWord_consumption start clause
      ((List.range' (start + 1) rest.length).flatMap (fun i => testWord i clause) ++ suffix)
      a (rest ++ A2) hrest_ne).1
    have hih := testChain_actd_cons rest A2 (start + 1) clause suffix hA2
    simp only [List.cons_append] at htw ⊢
    rw [htw, hih]
    show ALIGN.length + (rest.length * ALIGN.length + _) =
      (rest.length + 1) * ALIGN.length + _
    rw [Nat.add_mul, Nat.one_mul]; omega

/-- From ACTD, sentinel form: A1 testWords + endTestWord on x :: Q :: A2.
    Uses testChain_actd_cons to shift past A1, then endTestWord_consumption ACTD with y=Q. -/
theorem testChain_actd_end_new (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ []) :
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: PileType.Q :: A2))) ACTD =
    (A1.length + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from
    List.append_assoc ..]
  have htc := testChain_actd_cons A1 (x :: PileType.Q :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp)
  rw [htc]
  have hend := (endTestWord_consumption (j + A1.length) clause suffix x PileType.Q A2 hA2).2
  rw [if_pos rfl] at hend
  rw [hend.1]
  rw [show (A1.length + 1) * ALIGN.length = A1.length * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul]]
  omega

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
  -- 2. endTestWord_consumption ACTD case with y = Q
  have hend_raw := (endTestWord_consumption (j + k) clause suffix (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2).2
  rw [hQ, if_pos rfl] at hend_raw
  -- 3. Combine via rw
  rw [htc, show A1[k + 1] = PileType.Q from hQ, hend_raw.1]
  show k * ALIGN.length + (ALIGN.length + _) = (k + 1) * ALIGN.length + _
  rw [show (k + 1) * ALIGN.length = k * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul], Nat.add_assoc]

/-- From NACTD at activation site, sentinel form (6 segments).
    x activates (NACTD → ACTD), A1_mid stays ACTD, y is endTestWord variable, Q is sentinel. -/
theorem testChain_activate_end_new (j : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (A1_mid : List PileType) (y : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (hlit : matchesLiteral x j clause) :
    applyWord ((List.range' j (A1_mid.length + 1)).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1_mid.length + 1) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: A1_mid ++ y :: PileType.Q :: A2))) NACTD =
    (A1_mid.length + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  -- 1. Peel off the activating testWord
  rw [show (List.range' j (A1_mid.length + 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (j + A1_mid.length + 1) clause ++ suffix =
      testWord j clause ++
        ((List.range' (j + 1) A1_mid.length).flatMap (fun i => testWord i clause) ++
          endTestWord (j + A1_mid.length + 1) clause ++ suffix) from by
    rw [List.range'_succ, List.flatMap_cons]; simp only [List.append_assoc]]
  -- 2. testWord_consumption NACTD with matching literal → ACTD
  have htw := (testWord_consumption j clause
    ((List.range' (j + 1) A1_mid.length).flatMap (fun i => testWord i clause) ++
      endTestWord (j + A1_mid.length + 1) clause ++ suffix)
    x (A1_mid ++ y :: PileType.Q :: A2) (by simp)).2.2
  rw [if_pos hlit] at htw
  simp only [List.cons_append] at htw ⊢
  rw [htw]
  -- 3. testChain_actd_end_new on A1_mid ++ y :: Q :: A2
  rw [show j + A1_mid.length + 1 = (j + 1) + A1_mid.length from by omega]
  have hae := testChain_actd_end_new (j + 1) clause suffix A1_mid y A2 hA2
  rw [hae]
  -- 4. Arithmetic
  rw [show (A1_mid.length + 2) * ALIGN.length =
      ALIGN.length + (A1_mid.length + 1) * ALIGN.length from by
    rw [show A1_mid.length + 2 = 1 + (A1_mid.length + 1) from by omega,
        Nat.add_mul, Nat.one_mul]]
  omega

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

/-- NACTD with no matching literals: stays at exactly NACTD after shifting.
    Mirrors testChain_actd but uses the NACTD case with ¬matchesLiteral. -/
theorem testChain_nactd_old : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType) (hlen : k < types.length),
    (∀ i (hi : i < k), ¬matchesLiteral (types[i]'(by omega)) (start + i) clause) →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) NACTD =
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) NACTD
  | 0, _, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes, _ => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes, hno => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have hno0 : ¬matchesLiteral x start clause := by
      have := hno 0 (by omega); simp at this; exact this
    have htw := (testWord_consumption start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest).2.2
    rw [if_neg hno0] at htw
    have hih := testChain_nactd_old k (start + 1) clause suffix rest (by omega) (by
      intro i hi
      have := hno (i + 1) (by omega)
      simp only [List.length_cons, List.getElem_cons_succ] at this
      rw [show start + (i + 1) = start + 1 + i from by omega] at this
      exact this)
    show _ = (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) NACTD
    rw [Nat.succ_mul, htw, hih]; omega

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
    have htw := (testWord_consumption start clause
      ((List.range' (start + 1) rest.length).flatMap (fun i => testWord i clause) ++ suffix)
      a (rest ++ A2) hrest_ne).2.2
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
  -- 2. endTestWord_consumption NACTD case with y=Q, ¬matchesLiteral
  have hend_raw := (endTestWord_consumption (j + k) clause suffix (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2).2
  rw [hQ, if_pos rfl] at hend_raw
  rw [if_neg hno_end] at hend_raw
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
  -- 2. endTestWord_consumption NACTD case with y=Q, ¬matchesLiteral
  have hend := (endTestWord_consumption (j + A1.length) clause suffix x PileType.Q A2 hA2).2
  rw [if_pos rfl, if_neg hno_end] at hend
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

/-- Activation at the endTestWord, sentinel decomposition form.
    A1 = non-matching prefix, x = matching last variable, Q = sentinel. -/
theorem testChain_sat_end_eq (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (hml : matchesLiteral x (j + A1.length) clause)
    (hno : ∀ i (hi : i < A1.length), ¬matchesLiteral A1[i] (j + i) clause) :
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: PileType.Q :: A2))) NACTD =
    (A1.length + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  -- 1. Reassociate word, apply testChain_nactd
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from
    List.append_assoc ..]
  have htcn := testChain_nactd A1 (x :: PileType.Q :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp) hno
  rw [htcn]
  -- 2. endTestWord_consumption NACTD with matchesLiteral and y=Q
  have hend := (endTestWord_consumption (j + A1.length) clause suffix
    x PileType.Q A2 hA2).2
  rw [if_pos rfl, if_pos hml] at hend
  rw [hend.2]
  -- 3. Arithmetic
  rw [show (A1.length + 1) * ALIGN.length = A1.length * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul]]
  omega

/-- Case i₀ < k in sentinel form: activation during a regular testWord.
    A1_pre = non-matching prefix, x = matching activation site,
    A1_post = remaining variables (including endTestWord variable), Q = sentinel.
    Proof deferred until testChain_activate_end gets sentinel form. -/
theorem testChain_sat_end_lt_new (j : Nat) (clause : Clause) (suffix : List Action)
    (A1_pre : List PileType) (x : PileType) (A1_post : List PileType) (A2 : List PileType)
    (hA2 : A2 ≠ [])
    (hne : A1_post ≠ [])
    (hml : matchesLiteral x (j + A1_pre.length) clause)
    (hno : ∀ i (hi : i < A1_pre.length), ¬matchesLiteral A1_pre[i] (j + i) clause) :
    applyWord ((List.range' j (A1_pre.length + A1_post.length)).flatMap (fun i => testWord i clause) ++
              endTestWord (j + (A1_pre.length + A1_post.length)) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1_pre ++ x :: A1_post ++ PileType.Q :: A2))) NACTD =
    (A1_pre.length + A1_post.length + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  sorry

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
  -- 3. endTestWord_consumption NACTD with matchesLiteral and y=Q
  have hend := (endTestWord_consumption (j + k) clause suffix
    (A1[k]'(by omega)) PileType.Q A2 hA2).2
  rw [if_pos rfl, if_pos hml] at hend
  rw [hend.2]
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

/-- Preamble: clauseWord from START_POS reduces to testWords ++ endTestWord from NACTD,
    after factoring out A0 and applying start_clause_start. -/
theorem clauseWord_start_preamble (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hA1 : A1.length = n + 1) :
    applyWord (clauseWord n clause)
      (compile (virtualPileTypes ALIGN (A0 ++ A1 ++ A2))) (START_POS + A0.length * ALIGN.length) =
    A0.length * ALIGN.length +
      applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause)
        (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD := by
  -- 1. Factor out A0
  rw [show A0 ++ A1 ++ A2 = A0 ++ (A1 ++ A2) from List.append_assoc ..,
      virtualPileTypes_append,
      show START_POS + A0.length * ALIGN.length =
        (virtualPileTypes ALIGN A0).length + START_POS from by
        rw [virtualPileTypes_length]; omega,
      applyWord_compile_append_shift, virtualPileTypes_length]
  -- 2. Unfold clauseWord, reassociate as START_CLAUSE ++ rest
  unfold clauseWord
  rw [show START_CLAUSE ++ (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause =
      START_CLAUSE ++ ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause) from by simp [List.append_assoc]]
  -- 3. A1 is nonempty; start_clause_start → NACTD
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, A1 = t :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  rw [List.cons_append,
      start_clause_start _ t (rest ++ A2)]


/-- When A1 ends in Q and has no matching satisfying assignment,
    no matchesLiteral fires at any index. -/
theorem not_hasMatchingAssignment_no_matchesLiteral
    (n : Nat) (A1 : List PileType) (clause : Clause)
    (hA1 : A1.length = n + 1) (hQ : A1[n]'(by omega) = PileType.Q)
    (hno : ¬HasMatchingAssignment n A1 (satisfiesClause · clause)) :
    ∀ i (hi : i < n), ¬matchesLiteral (A1[i]'(by omega)) i clause := by
  -- A1 = init ++ [Q], init = embedVars vars
  obtain ⟨init, last, hsplit, hilen⟩ := list_split_last A1 (by intro h; simp [h] at hA1)
  have hlast : last = PileType.Q := by
    have h1 : A1[n]'(by omega) = last := by
      simp only [hsplit]
      rw [List.getElem_append_right (by omega)]
      simp
    rw [← h1]; exact hQ
  have hinit_len : init.length = n := by omega
  obtain ⟨vars, hvlen, hvars⟩ := embedVars_surjective init
  -- ¬satisfiesClause
  have hnotsat : ¬satisfiesClause vars clause := by
    intro hsat
    exact hno ⟨vars, hvlen ▸ hinit_len, hlast ▸ hvars ▸ hsplit, hsat⟩
  -- Pointwise ¬matchesLiteral
  intro i hi hml
  apply hnotsat
  -- A1[i] = init[i] = embedVar vars[i]
  have hAi : A1[i]'(by omega) = init[i]'(by omega) := by
    simp only [hsplit]; rw [List.getElem_append_left (by omega)]
  rw [hAi] at hml
  simp only [← hvars, embedVars, List.getElem_map] at hml
  -- hml : matchesLiteral (embedVar vars[i]) i clause
  rw [satisfiesClause_iff_matchesLiteral]
  have hvi : i < vars.length := by rw [hvlen]; omega
  exact ⟨i, hvi, by
    have : vars.getD i false = vars[i]'hvi := by
      simp [List.getD, List.getElem?_eq_getElem hvi]
    rw [this]
    exact hml⟩

/-- When vars satisfies a clause, there is a first index where matchesLiteral fires.
    Returns the first matching index with proof it's minimal. -/
theorem satisfiesClause_first_matchesLiteral
    (vars : List Bool) (clause : Clause)
    (hsat : satisfiesClause vars clause) :
    ∃ i₀ : Fin vars.length,
      matchesLiteral (embedVar vars[i₀]) i₀ clause ∧
      ∀ j : Fin vars.length, j < i₀ →
        ¬matchesLiteral (embedVar vars[j]) j clause := by
  -- From satisfiesClause, get some matching index
  rw [satisfiesClause_iff_matchesLiteral] at hsat
  obtain ⟨i, hi, hml⟩ := hsat
  have hml' : matchesLiteral (embedVar vars[i]) i clause := by
    rwa [show vars.getD i false = vars[i] from by
      simp [List.getD, List.getElem?_eq_getElem hi]] at hml
  -- Find the minimum by strong induction on the index
  have : ∀ k (hk : k < vars.length),
      matchesLiteral (embedVar vars[k]) k clause →
      ∃ i₀ : Fin vars.length,
        matchesLiteral (embedVar vars[i₀]) i₀ clause ∧
        ∀ j : Fin vars.length, j < i₀ →
          ¬matchesLiteral (embedVar vars[j]) j clause := by
    intro k
    induction k using Nat.strongRecOn with
    | _ k ih =>
      intro hk hmlk
      by_cases hex : ∃ j : Fin vars.length, j.val < k ∧
          matchesLiteral (embedVar vars[j]) j clause
      · obtain ⟨⟨j, hj⟩, hjk, hmlj⟩ := hex
        exact ih j hjk hj hmlj
      · exact ⟨⟨k, hk⟩, hmlk, fun j hj hc =>
          hex ⟨j, hj, hc⟩⟩
  exact this i hi hml'

/-- clauseWord from START_POS: if a satisfying assignment matches A1, reaches END_POS;
    otherwise reaches the penalty zone. -/
theorem clauseWord_start_sat (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    ∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) =
        END_POS + (k + n) * m := by
  simp only []
  intro vars hvars hA1eq hsat
  -- 1. Preamble: reduce to NACTD on testWords ++ endTestWord
  rw [clauseWord_start_preamble n clause A0 A1 A2 hA1]
  -- 2. Find first activation index
  obtain ⟨⟨i₀, hi₀v⟩, hml_ev, hno_ev⟩ :=
    satisfiesClause_first_matchesLiteral vars clause hsat
  -- 3. Substitute A1 = embedVars vars ++ [Q] everywhere
  subst hA1eq
  have hevlen : (embedVars vars).length = n := by simp [embedVars, hvars]
  have hi₀n : i₀ < n := by omega
  -- Convert embedVar vars[i] to (embedVars vars ++ [Q])[i]
  have embed_eq : ∀ i (hi : i < n),
      (embedVars vars ++ [PileType.Q])[i]'(by simp [hevlen]; omega) = embedVar vars[i] := by
    intro i hi
    rw [List.getElem_append_left (by simp [hevlen]; omega)]
    simp [embedVars]
  have hml : matchesLiteral
      ((embedVars vars ++ [PileType.Q])[i₀]'(by simp [hevlen]; omega)) i₀ clause := by
    rw [embed_eq i₀ hi₀n]; exact hml_ev
  have hno : ∀ i (hi : i < i₀),
      ¬matchesLiteral
        ((embedVars vars ++ [PileType.Q])[i]'(by simp [hevlen]; omega)) i clause := by
    intro i hi hc
    exact hno_ev ⟨i, by omega⟩ hi (by rwa [embed_eq i (by omega)] at hc)
  -- 4. Apply testChain_sat_end_zero
  have hQ : (embedVars vars ++ [PileType.Q])[(n - 1) + 1]'(by simp [hevlen]; omega) =
      PileType.Q := by
    simp [List.getElem_append, hevlen, show n - 1 + 1 = n from by omega]
  have htse := testChain_sat_end_zero (n - 1) i₀ clause
    (embedVars vars ++ [PileType.Q]) A2
    (by simp [hevlen]; omega) hA2 hQ (by omega) hml hno
  simp only [show applyWord [] _ END_POS = END_POS from rfl] at htse
  rw [htse, show n - 1 + 1 = n from by omega, Nat.add_mul]
  omega

/-- clauseWord from START_POS without satisfying assignment → penalty.

    Proof:
    1. Factor out A0 via applyWord_compile_append_shift. Unfold clauseWord.
       start_clause_start → NACTD on A1 ++ A2, applying testWords(0..n-2) ++ endTestWord(n-1).
    2. Case split on A1[n] (last element):
       2a. A1[n] = Q: Every PileType is Q or S, so A1 = embedVars vars ++ [Q] for unique vars.
           ¬HasMatchingAssignment → ¬satisfiesClause vars clause.
           Via satisfiesClause_iff_matchesLiteral, no matchesLiteral fires at any index.
           testChain_nactd_end with k=n-1 → ≥ (n+1)*m + CHAIN_DISQ.
       2b. A1[n] = S (≠ Q): Monotonicity (NACTD=3 ≥ ACTD=2), so bound by ACTD path.
           testChain_actd for n-1 steps + endTestWord_consumption ACTD with y≠Q → ≥ nextBad.
           Total: (n-1)*m + 2*m + CHAIN_DISQ = (n+1)*m + CHAIN_DISQ. -/
theorem clauseWord_start_nonsat (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    ¬ HasMatchingAssignment n A1 (satisfiesClause · clause) →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) ≥
        CHAIN_DISQ + (k + n + 1) * m := by
  simp only []
  intro hno
  rw [clauseWord_start_preamble n clause A0 A1 A2 hA1]
  -- Goal: A0.length * m + applyWord (testWords ++ endTestWord) (vpt (A1 ++ A2)) NACTD
  --       ≥ CHAIN_DISQ + (A0.length + n + 1) * m
  -- Suffices to show inner ≥ (n+1)*m + CHAIN_DISQ
  suffices h : applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
      endTestWord (n - 1) clause) (compile (virtualPileTypes ALIGN (A1 ++ A2))) NACTD ≥
      (n + 1) * ALIGN.length + CHAIN_DISQ by
    rw [show A0.length + n + 1 = A0.length + (n + 1) from by omega, Nat.add_mul]; omega
  -- Case split on last element of A1
  cases ht : A1[n]'(by omega) with
  | Q =>
    -- Case 2a: A1[n] = Q, so A1 = embedVars vars ++ [Q] for some vars.
    -- Steps 1-3: no matchesLiteral fires anywhere
    have hnoml := not_hasMatchingAssignment_no_matchesLiteral n A1 clause hA1 ht hno
    -- Step 4: testChain_nactd_end with k=n-1, j=0
    simp only [List.range_eq_range']
    have hQ' : A1[(n - 1) + 1]'(by omega) = PileType.Q := by
      simp only [show n - 1 + 1 = n from by omega]; exact ht
    have hte := testChain_nactd_end_old (n - 1) 0 clause [] A1 A2 (by omega) hA2 hQ'
      (by intro i hi; simp; exact hnoml i (by omega))
      (by simp; exact hnoml (n - 1) (by omega))
    simp only [show 0 + (n - 1) = n - 1 from by omega,
      List.append_nil,
      show applyWord ([] : List Action) (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ from rfl] at hte
    show _ ≥ (n + 1) * ALIGN.length + CHAIN_DISQ
    rw [show n + 1 = (n - 1) + 2 from by omega]
    exact hte
  | S =>
    -- Case 2b: A1[n] = S (≠ Q).
    -- Goal: applyWord (testWords ++ endTestWord) machine NACTD ≥ (n+1)*m + CHAIN_DISQ
    -- Let W = testWords ++ endTestWord, M = machine.
    -- Step 1: applyWord_mono (ACTD ≤ NACTD): applyWord W M ACTD ≤ applyWord W M NACTD.
    -- Step 2: testChain_actd (n-1) 0 (suffix=endTestWord): applyWord W M ACTD
    --         = (n-1)*m + applyWord (endTestWord) M' ACTD
    --         where M' = vpt ALIGN (A1[n-1] :: A1[n] :: A2).
    -- Step 3: Substitute A1[n] = S in Step 2 result.
    -- Step 4: endTestWord_consumption ACTD with y=S≠Q, suffix=[]:
    --         applyWord (endTestWord) M' ACTD ≥ 2*m + CHAIN_DISQ.
    -- Step 5: Combine Steps 1-4:
    --         applyWord W M NACTD ≥ applyWord W M ACTD
    --           = (n-1)*m + applyWord (endTestWord) M' ACTD
    --           ≥ (n-1)*m + 2*m + CHAIN_DISQ = (n+1)*m + CHAIN_DISQ.
    -- Step 1: mono
    have hmono := applyWord_mono
      ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++ endTestWord (n - 1) clause)
      (virtualPileTypes ALIGN (A1 ++ A2))
      (show ACTD ≤ NACTD from by decide)
    -- Step 2: testChain_actd, using list_drop_append_two_last so indices use A1[n] not A1[n-1+1]
    simp only [List.range_eq_range'] at hmono ⊢
    have htc := testChain_actd (n - 1) 0 clause
      (endTestWord (n - 1) clause) (A1 ++ A2) (by simp [hA1]; omega)
    rw [list_drop_append_two_last A1 A2 n hA1 hn] at htc
    -- Steps 3-4: endTestWord_consumption ACTD with y = S ≠ Q
    have hend := (endTestWord_consumption (n - 1) clause []
      (A1[n - 1]'(by omega)) (A1[n]'(by omega)) A2 hA2).2
    simp only [ht, show PileType.S = PileType.Q ↔ False from by decide,
      false_iff, ite_false, List.append_nil,
      show applyWord ([] : List Action) (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ from rfl] at hend
    -- Step 5: calc chain
    simp only [ht] at htc
    calc (n + 1) * ALIGN.length + CHAIN_DISQ
        = (n - 1) * ALIGN.length + 2 * ALIGN.length + CHAIN_DISQ := by
          rw [show n + 1 = (n - 1) + 2 from by omega, Nat.add_mul]
      _ ≤ (n - 1) * ALIGN.length +
            applyWord (endTestWord (n - 1) clause)
              (compile (virtualPileTypes ALIGN (A1[n - 1]'(by omega) :: PileType.S :: A2))) ACTD :=
          Nat.add_le_add_left hend _
      _ = applyWord _ _ ACTD := htc.symm
      _ ≤ applyWord _ _ NACTD := hmono

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
    have htw := (testWord_consumption start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest).2.1
    have hih := testChain_disq k (start + 1) clause suffix rest (by omega)
    show _ >= (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) CLAUSE_DISQ
    rw [Nat.succ_mul]; omega

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

/-- testWords ++ endTestWord from CLAUSE_DISQ: specialization of testChain_disq_end'
    with k = n-1, j = 0. -/
theorem testChain_disq_end (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
              endTestWord (n - 1) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    (n + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  rw [show List.range (n - 1) = List.range' 0 (n - 1) from List.range_eq_range' ..,
      show (n + 1) = (n - 1 + 2) from by omega,
      show endTestWord (n - 1) = endTestWord (0 + (n - 1)) from by simp]
  exact testChain_disq_end' (n - 1) 0 clause suffix A1 A2 (by omega) hA2

/-- clauseWord in consumption form from CHAIN_DISQ: consumes n+1 blocks.

    Proof: unfold clauseWord, start_clause_disq + testChain_disq_end. -/
theorem clauseWord_chain_consumption (n : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hn : n ≥ 1)
    (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord (clauseWord n clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CHAIN_DISQ ≥
    (n + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  -- Unfold clauseWord and reassociate
  unfold clauseWord
  rw [show START_CLAUSE ++ (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause ++ suffix =
      START_CLAUSE ++ ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
        endTestWord (n - 1) clause ++ suffix) from by simp [List.append_assoc]]
  -- A1 is nonempty
  obtain ⟨t, rest, rfl⟩ : ∃ t rest, A1 = t :: rest := by
    match A1, hA1 with | a :: as, _ => exact ⟨a, as, rfl⟩
  -- start_clause_disq: from CHAIN_DISQ, ≥ rest from CLAUSE_DISQ
  have hsc := start_clause_disq
    ((List.range (n - 1)).flatMap (fun i => testWord i clause) ++
      endTestWord (n - 1) clause ++ suffix)
    t (rest ++ A2)
  -- testChain_disq_end: from CLAUSE_DISQ, consumes n+1 blocks
  have hte := testChain_disq_end n clause suffix (t :: rest) A2 hn hA1 hA2
  exact Nat.le_trans hte (hsc)

/-- clauseWord from CHAIN_DISQ: penalty propagates unconditionally.

    English proof:
    1. Factor out A0 via applyWord_compile_append_shift:
       goal reduces to k*m + inner ≥ CHAIN_DISQ + (k+n+1)*m,
       i.e., inner ≥ CHAIN_DISQ + (n+1)*m.
    2. Apply clauseWord_chain_consumption (with empty suffix) on A1 ++ A2:
       inner ≥ (n+1)*m + applyWord [] (compile (vpt ALIGN A2)) CHAIN_DISQ
            = (n+1)*m + CHAIN_DISQ. ∎ -/
theorem clauseWord_chain (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    applyWord (clauseWord n clause) (compile types) (CHAIN_DISQ + k * m) ≥
      CHAIN_DISQ + (k + n + 1) * m := by
  simp only []
  -- 1. Factor out A0
  rw [show A0 ++ A1 ++ A2 = A0 ++ (A1 ++ A2) from List.append_assoc ..,
      virtualPileTypes_append,
      show CHAIN_DISQ + A0.length * ALIGN.length =
        (virtualPileTypes ALIGN A0).length + CHAIN_DISQ from by
        rw [virtualPileTypes_length]; omega,
      applyWord_compile_append_shift, virtualPileTypes_length]
  -- 2. Apply clauseWord_chain_consumption with empty suffix
  have hcc := clauseWord_chain_consumption n clause [] A1 A2 hn hA1 hA2
  rw [List.append_nil, show applyWord ([] : List Action)
    (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ from rfl] at hcc
  -- hcc: applyWord clauseWord ... CHAIN_DISQ ≥ (n+1)*ALIGN.length + CHAIN_DISQ
  -- Goal: A0*AL + applyWord clauseWord ... CHAIN_DISQ ≥ CHAIN_DISQ + (A0+n+1)*AL
  -- 3. Arithmetic: (A0+n+1)*AL = A0*AL + (n+1)*AL, then omega combines with hcc
  rw [show A0.length + n + 1 = A0.length + (n + 1) from by omega, Nat.add_mul]
  omega

/-- Combined clauseWord correctness, assembling start and chain parts. -/
theorem clauseWord_correct (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    (∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) =
        END_POS + (k + n) * m)
    ∧
    (¬ HasMatchingAssignment n A1 (satisfiesClause · clause) →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) ≥
        CHAIN_DISQ + (k + n + 1) * m)
    ∧
    applyWord (clauseWord n clause) (compile types) (CHAIN_DISQ + k * m) ≥
      CHAIN_DISQ + (k + n + 1) * m :=
  ⟨clauseWord_start_sat n clause A0 A1 A2 hn hA1 hA2,
   clauseWord_start_nonsat n clause A0 A1 A2 hn hA1 hA2,
   clauseWord_chain n clause A0 A1 A2 hn hA1 hA2⟩

/-- clauseWord from START_POS on replicated types: if a matching assignment satisfies the
    clause, reaches END_POS + n * ALIGN.length; otherwise reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct parts 1 and 2 for the List.replicate m .Q form. -/
theorem clauseWord_sat (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    (∀ vars : List Bool, vars.length = n → xs = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars c →
      applyWord (clauseWord n c) (compile types) START_POS =
        END_POS + n * ALIGN.length)
    ∧
    (¬ HasMatchingAssignment n xs (satisfiesClause · c) →
      CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c) (compile types) START_POS) := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN ([] ++ xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : m - 1 ≥ 1 := by omega
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := clauseWord_correct n c [] xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2
  simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hcw
  constructor
  · exact hcw.1
  · intro hno
    have := hcw.2.1 hno
    calc CHAIN_DISQ + xs.length * ALIGN.length
        = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
      _ ≤ _ := this

/-- clauseWord from ≥ CHAIN_DISQ on replicated types always reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct part 3 for the List.replicate m .Q form. -/
theorem clauseWord_penalty (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (s : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) (hs : CHAIN_DISQ ≤ s) :
    CHAIN_DISQ + xs.length * ALIGN.length ≤
      applyWord (clauseWord n c)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))) s := by
  -- Rewrite types to clauseWord_correct form
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN ([] ++ xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  -- clauseWord_correct part 3 with A0=[], A1=xs, A2=remaining
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := (clauseWord_correct n c [] xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2).2.2
  simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hcw
  -- mono: result(s) ≥ result(CHAIN_DISQ) ≥ bound
  calc CHAIN_DISQ + xs.length * ALIGN.length
      = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
    _ ≤ applyWord (clauseWord n c) _ CHAIN_DISQ := hcw
    _ ≤ applyWord (clauseWord n c) _ s :=
        applyWord_mono (clauseWord n c) _ hs
