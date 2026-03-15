/-
  TestChain: consumption-form lemmas for a sequence of testWords.

  ## The consumption form

  The key structural property of all lemmas here is the *consumption form*:

    applyWord (testWords ++ suffix) machine state =
      offset + applyWord suffix machine' state'

  This factors the behavior of a word sequence into a fixed offset (the cost
  of the sequence itself) plus the behavior of the suffix on the residual
  machine.  It is what makes these lemmas composable: each layer hands off to
  the next via a concrete suffix machine.

  ## Index-based vs. destructured parameterization

  The individual `testWord_consumption_*` lemmas in TestConsume use `x :: rest`
  for the pile-type list: one word consumes `x` from the front and leaves
  `rest`.  When chaining k test words, there are two equivalent ways to name
  the boundary:

  **Index form** (`types` + `k < types.length`, conclusion mentions `types.drop k`):
    Falls out naturally from naïve induction — each step increments k and
    peels one element.  Convenient when the caller reasons by count.

  **Destructured form** (`A1 ++ A2`, conclusion mentions `A2` directly):
    The caller pre-splits the list and names both halves; no `drop` expression
    appears in the conclusion.  Convenient when the caller already holds
    concrete `A1` and `A2`.

  The two forms are logically equivalent (set `A1 = types.take k`,
  `A2 = types.drop k`); conversion is always `List.take_append_drop` plus a
  length lemma.  **Neither form has clear supremacy**: destructured tends to
  win at call sites that already name the halves; index tends to win when the
  caller is reasoning by count and would have to construct the split
  artificially.  Because the conversion is cheap and local, the choice can be
  revisited per-lemma once all lemmas are in consumption form.

  The lemmas in this file use the destructured form.  The old index-form
  variants (`testChain_actd`, `testChain_nactd_old` in ClauseWord.lean) are
  dead code pending deletion.

  ## Regular chains vs. end-capped chains

  A clauseWord gadget for a clause with n variables consists of a START_CLAUSE
  preamble, then n-1 testWords, followed by one endTestWord.  This gives two natural sub-problems:

  **Regular chains** cover a prefix of k testWords only.  Each testWord uses the
  same activation gadget and simply shifts the machine state forward by one block.
  The ending state (ACTD, NACTD, or ≥ CLAUSE_DISQ) is passed on to the suffix.

  **End-capped chains** cover k testWords followed by a single endTestWord.
  The endTestWord uses a different (end-activation) gadget that closes off the
  clause: if the clause is satisfied it reaches END_POS; otherwise it reaches
  the penalty zone (≥ CHAIN_DISQ).  End-capped chains give a complete picture
  of one clauseWord's contribution to the machine trace.

  The single-step building blocks for both kinds of chain are in TestConsume.lean.

  ## Plain-chain lemmas

  Three lemmas cover a sequence of k testWords from a given start state:

  - **`testChain_actd_cons`**: from ACTD, shifts past A1, stays at ACTD (= form).
  - **`testChain_disq_cons`**: from CLAUSE_DISQ, shifts past A1, stays ≥ CLAUSE_DISQ.
  - **`testChain_nactd_cons`**: from NACTD, shifts past A1, landing at ACTD if
    `∃ i : Fin A1.length, matchesLiteral A1[i] (start+i) clause`, else NACTD.

  ## End-capped lemmas

  Five lemmas cover a sequence of testWords followed by an endTestWord.  The
  end-capped form arises at the boundary of a clauseWord gadget.

  - **`testChain_disq_end'`**: from CLAUSE_DISQ, k testWords + endTestWord → ≥ CHAIN_DISQ.
  - **`testChain_actd_end_new`**: from ACTD, Q sentinel → = END_POS.
  - **`testChain_actd_end_disq`**: from ACTD, non-Q sentinel → ≥ CHAIN_DISQ.
  - **`testChain_nactd_end_endpos`**: from NACTD, Q sentinel + any activation → = END_POS.
  - **`testChain_nactd_end_disq_nomatch`**: from NACTD, Q sentinel + no match → ≥ CHAIN_DISQ.
  - **`testChain_nactd_end_disq_noQ`**: from NACTD, non-Q sentinel → ≥ CHAIN_DISQ.
  - **`testChain_nactd_end_disq`**: trivially combines the two NACTD disq cases.

  ### Design note: NACTD end-capped (4-lemma compromise)

  The NACTD end-capped case has two outcome branches (= END_POS vs. ≥ CHAIN_DISQ)
  and the disq branch splits further on the sentinel (Q or non-Q).  Two designs
  were considered:

  **3 lemmas** — one per outcome sub-case, each with a single clean hypothesis.
  Maps 1-1 onto the branches of `clauseWord_start_nonsat_cons`, but leaves an
  internal Q/S split in that proof.

  **2 lemmas** — combine the two disq sub-cases into one, absorbing the split
  internally.  Gives a cleaner `clauseWord_start_nonsat_cons` (no case split
  needed), but makes the combined disq lemma internally more complex.

  Rather than commit to either, all three focused lemmas are provided plus a
  trivial combined one (`testChain_nactd_end_disq`).  Call sites use whichever
  form fits best; the two-line combined lemma costs nothing extra.
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

/-- When A1 has exactly k+2 elements, dropping the first k gives the last two. -/
theorem list_drop_two {α : Type} (A1 : List α) (k : Nat) (hA1 : A1.length = k + 2) :
    A1.drop k = [A1[k]'(by omega), A1[k + 1]'(by omega)] := by
  have hdlen : (A1.drop k).length = 2 := by rw [List.length_drop, hA1]; omega
  match h : A1.drop k, hdlen with
  | [a, b], _ =>
    simp; constructor
    · have := List.getElem_drop (i := k) (j := 0) (h := by omega) A1; simp [h] at this; exact this
    · have := List.getElem_drop (i := k) (j := 1) (h := by omega) A1; simp [h] at this; exact this

/-- From CLAUSE_DISQ: k testWords (indices j..j+k-1) + endTestWord (j+k) reach
    penalty zone, consuming k+2 blocks total.

    Proof:
    1. Reassociate word as testWords ++ (endTestWord ++ suffix).
    2. testChain_disq_cons on (A1.take k) ++ (A1.drop k ++ A2): shifts by k*m.
    3. Rewrite A1.drop k = [A1[k], A1[k+1]] via list_drop_two.
    4. endTestWord_consumption_disq: ≥ 2*m + suffix from CHAIN_DISQ on A2.
    5. Total: k*m + 2*m = (k+2)*m. -/
theorem testChain_disq_end' (k j : Nat) (clause : Clause) (suffix : List Action)
    (A1 A2 : List PileType) (hA1 : A1.length = k + 2) (hA2 : A2 ≠ []) :
    applyWord ((List.range' j k).flatMap (fun i => testWord i clause) ++
              endTestWord (j + k) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) CLAUSE_DISQ ≥
    (k + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ := by
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have hdrop_ne : A1.drop k ++ A2 ≠ [] := by
    have hne : A1.drop k ≠ [] := by
      intro h
      have := congrArg List.length h
      simp [List.length_drop, hA1] at this
      omega
    intro h; exact hne (List.append_eq_nil.mp h).1
  have htc := testChain_disq_cons (A1.take k) (A1.drop k ++ A2) j clause
    (endTestWord (j + k) clause ++ suffix) hdrop_ne
  rw [show A1.take k ++ (A1.drop k ++ A2) = A1 ++ A2 from by
      rw [← List.append_assoc, List.take_append_drop],
    show (A1.take k).length = k from by rw [List.length_take]; omega,
    show A1.drop k ++ A2 = A1[k]'(by omega) :: A1[k + 1]'(by omega) :: A2 from by
      rw [list_drop_two A1 k hA1]; simp] at htc
  have hend := endTestWord_consumption_disq (j + k) clause suffix
    (A1[k]'(by omega)) (A1[k + 1]'(by omega)) A2 hA2
  show _ ≥ (k + 2) * ALIGN.length + _
  rw [show (k + 2) * ALIGN.length = k * ALIGN.length + 2 * ALIGN.length from by rw [Nat.add_mul]]
  omega

/-- From ACTD, Q-sentinel: A1 testWords + endTestWord on x :: Q :: A2 reaches END_POS. -/
theorem testChain_actd_end_new (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ []) :
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: PileType.Q :: A2))) ACTD =
    (A1.length + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htc := testChain_actd_cons A1 (x :: PileType.Q :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp)
  rw [htc]
  have hend := endTestWord_consumption_actd (j + A1.length) clause suffix x PileType.Q A2 hA2
  rw [if_pos rfl] at hend
  rw [hend, show (A1.length + 1) * ALIGN.length = A1.length * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul]]
  omega

/-- From ACTD, non-Q sentinel: A1 testWords + endTestWord on x :: et :: A2 reaches penalty
    (≥ CHAIN_DISQ) when et ≠ Q. -/
theorem testChain_actd_end_disq (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x et : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (het : et ≠ PileType.Q) :
    (A1.length + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ ≤
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: et :: A2))) ACTD := by
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htc := testChain_actd_cons A1 (x :: et :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp)
  rw [htc]
  have hend := endTestWord_consumption_actd (j + A1.length) clause suffix x et A2 hA2
  rw [if_neg het] at hend
  rw [show (A1.length + 2) * ALIGN.length = A1.length * ALIGN.length + 2 * ALIGN.length from by
    rw [Nat.add_mul]]
  omega

/-- From NACTD, non-Q sentinel: chain + endTestWord reaches penalty regardless of activation.
    Case splits on whether chain activates:
    - ACTD branch: delegates to testChain_actd_end_disq (empty prefix).
    - NACTD branch: endTestWord_consumption_nactd else branch (et ≠ Q). -/
theorem testChain_nactd_end_disq_noQ (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x et : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (het : et ≠ PileType.Q) :
    (A1.length + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ ≤
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: et :: A2))) NACTD := by
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htcn := testChain_nactd_cons A1 (x :: et :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp)
  rw [htcn, show (A1.length + 2) * ALIGN.length = A1.length * ALIGN.length + 2 * ALIGN.length from by
    rw [Nat.add_mul]]
  rcases Classical.em (∃ i : Fin A1.length, matchesLiteral A1[i] (j + ↑i) clause) with hact | hnoact
  · rw [if_pos hact]
    have hend := testChain_actd_end_disq (j + A1.length) clause suffix [] x et A2 hA2 het
    simp at hend; omega
  · rw [if_neg hnoact]
    have hend := endTestWord_consumption_nactd (j + A1.length) clause suffix x et A2 hA2
    rw [if_neg (fun ⟨heq, _⟩ => het heq)] at hend; omega

/-- From NACTD, Q sentinel, no match anywhere: chain + endTestWord reaches penalty. -/
theorem testChain_nactd_end_disq_nomatch (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (hno : ∀ i (hi : i < A1.length), ¬matchesLiteral A1[i] (j + i) clause)
    (hno_end : ¬matchesLiteral x (j + A1.length) clause) :
    (A1.length + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ ≤
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: PileType.Q :: A2))) NACTD := by
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
  have htcn := testChain_nactd_cons A1 (x :: PileType.Q :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp)
  rw [htcn, if_neg (by rintro ⟨⟨i, hi⟩, hm⟩; exact hno i hi hm),
      show (A1.length + 2) * ALIGN.length = A1.length * ALIGN.length + 2 * ALIGN.length from by
        rw [Nat.add_mul]]
  have hend := endTestWord_consumption_nactd (j + A1.length) clause suffix x PileType.Q A2 hA2
  rw [if_neg (fun ⟨_, h⟩ => hno_end h)] at hend
  omega

/-- From NACTD, Q sentinel, no activation anywhere → ≥ CHAIN_DISQ.
    Trivially combines testChain_nactd_end_disq_noQ and testChain_nactd_end_disq_nomatch. -/
theorem testChain_nactd_end_disq (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x et : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (h : et ≠ PileType.Q ∨
         (et = PileType.Q ∧ ¬matchesLiteral x (j + A1.length) clause ∧
          ∀ i (hi : i < A1.length), ¬matchesLiteral A1[i] (j + i) clause)) :
    (A1.length + 2) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ ≤
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: et :: A2))) NACTD := by
  rcases h with het | ⟨rfl, hno_end, hno⟩
  · exact testChain_nactd_end_disq_noQ j clause suffix A1 x et A2 hA2 het
  · exact testChain_nactd_end_disq_nomatch j clause suffix A1 x A2 hA2 hno hno_end

/-- Helper for `testChain_nactd_end_endpos`: the sub-case where the chain does not activate
    but the endTestWord literal matches (x at position j + A1.length).
    Extracted as a named lemma because `testChain_nactd_end_endpos` case-splits on chain
    activation first, and this covers the remaining `hnoact` branch cleanly.
    Not part of the planned 4-lemma API; candidate for inlining. -/
theorem testChain_sat_end_eq (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (hml : matchesLiteral x (j + A1.length) clause)
    (hno : ∀ i (hi : i < A1.length), ¬matchesLiteral A1[i] (j + i) clause) :
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: PileType.Q :: A2))) NACTD =
    (A1.length + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from
    List.append_assoc ..]
  have htcn := testChain_nactd_cons A1 (x :: PileType.Q :: A2) j clause
    (endTestWord (j + A1.length) clause ++ suffix) (by simp)
  rw [if_neg (by rintro ⟨⟨i, hi⟩, hm⟩; exact hno i hi hm)] at htcn
  rw [htcn]
  have hend := endTestWord_consumption_nactd (j + A1.length) clause suffix
    x PileType.Q A2 hA2
  rw [if_pos ⟨rfl, hml⟩] at hend
  rw [hend]
  rw [show (A1.length + 1) * ALIGN.length = A1.length * ALIGN.length + ALIGN.length from by
    rw [Nat.add_mul, Nat.one_mul]]
  omega

/-- From NACTD, Q sentinel, some activation (chain or end) → = END_POS.
    Case splits on chain activation:
    - Chain activates: testChain_nactd_cons ACTD branch + testChain_actd_end_new (empty prefix).
    - No chain activation: end must match; delegates to testChain_sat_end_eq. -/
theorem testChain_nactd_end_endpos (j : Nat) (clause : Clause) (suffix : List Action)
    (A1 : List PileType) (x : PileType) (A2 : List PileType) (hA2 : A2 ≠ [])
    (h : (∃ i : Fin A1.length, matchesLiteral A1[i] (j + ↑i) clause) ∨
         matchesLiteral x (j + A1.length) clause) :
    applyWord ((List.range' j A1.length).flatMap (fun i => testWord i clause) ++
              endTestWord (j + A1.length) clause ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ x :: PileType.Q :: A2))) NACTD =
    (A1.length + 1) * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: A2))) END_POS := by
  rcases Classical.em (∃ i : Fin A1.length, matchesLiteral A1[i] (j + ↑i) clause) with hact | hnoact
  · rw [show _ ++ endTestWord _ _ ++ suffix = _ ++ (endTestWord _ _ ++ suffix) from List.append_assoc ..]
    have htcn := testChain_nactd_cons A1 (x :: PileType.Q :: A2) j clause
      (endTestWord (j + A1.length) clause ++ suffix) (by simp)
    rw [htcn, if_pos hact]
    have hend := testChain_actd_end_new (j + A1.length) clause suffix [] x A2 hA2
    simp at hend
    rw [hend, show (A1.length + 1) * ALIGN.length = A1.length * ALIGN.length + ALIGN.length from by
      rw [Nat.add_mul, Nat.one_mul]]
    omega
  · have hml : matchesLiteral x (j + A1.length) clause := by
      rcases h with hact | hml
      · exact absurd hact hnoact
      · exact hml
    have hno : ∀ i (hi : i < A1.length), ¬matchesLiteral A1[i] (j + i) clause :=
      fun i hi hm => hnoact ⟨⟨i, hi⟩, hm⟩
    exact testChain_sat_end_eq j clause suffix A1 x A2 hA2 hml hno
