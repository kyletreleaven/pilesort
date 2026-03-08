/-
  Test chain end lemmas: combining testWord chains with endTestWord.

  These combine testChain_actd/testChain_disq (from ClauseWord) with
  endTestWord_consumption to give end-to-end results for the
  testWords ++ endTestWord portion of clauseWord.

  Generalized to start from any index j, so the same lemma covers:
  - j=0: full chain from the beginning (used by clauseWord_chain_consumption)
  - j>0: tail chain after activation (used by clauseWord_start satisfying case)
-/
import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.Activation
import PileSort.Gadgets.StartClause

def litMatches (lp : LitPresence) (x : PileType) : Prop :=
  (lp = .pos ∧ x = .Q) ∨ (lp = .neg ∧ x = .S)

instance (lp : LitPresence) (x : PileType) : Decidable (litMatches lp x) := by
  unfold litMatches; infer_instance

def matchesLiteral (x: PileType) (i : Nat) (clause: Clause): Prop :=
  litMatches (clause.getD i .absent) x

instance (x: PileType) (i : Nat) (clause: Clause) : Decidable (matchesLiteral x i clause) := by
  unfold matchesLiteral; infer_instance

theorem matchesLiteral_eq_litMatches (x : PileType) (i : Nat) (clause : Clause) :
    matchesLiteral x i clause = litMatches (clause.getD i .absent) x := rfl

/-- From ACTD: testWord stays activated, shifting by one block.

    Proof plan:
    1. Prove a helper (by `decide` over LitPresence × PileType × PileType)
       that for all lp, x, y:
         applyWord (match lp with .pos => POS | .neg => NEG | .absent => DK)
           (compile (vpt ALIGN [x, y])) ACTD = ACTD + ALIGN.length.
       This avoids case-splitting on the word; the ACTD branch of activationProp
       fires regardless of which word is used.
    2. Since rest ≠ [], write rest = y :: rest'. Lift to the full machine via
       `gadget_lift_eq` with window=[x,y], B=rest'.
    3. `applyWord_append` splits testWord ++ suffix, substitute the gadget result,
       then `applyWord_compile_append_shift` shifts past the consumed block. -/
theorem testWord_consumption_actd
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (testWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: rest))) ACTD =
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest)) ACTD
    := by
  -- 1. Gadget: ACTD → ACTD + m for any word in {POS, NEG, DK}  (activation_correct_actd)
  -- 2. Decompose rest = y :: rest'
  obtain ⟨y, rest', rfl⟩ : ∃ y rest', rest = y :: rest' := by
    match rest, hrest with | y :: rest', _ => exact ⟨y, rest', rfl⟩
  -- Specialize to testWord
  have hgadget : applyWord (testWord i clause)
      (compile (virtualPileTypes ALIGN [x, y])) ACTD = ACTD + ALIGN.length := by
    unfold testWord; split <;> exact activation_correct_actd (by simp) x y
  -- 3. Lift to full machine via gadget_lift_eq (window=[x,y], B=rest')
  have hlift := gadget_lift_eq (testWord i clause) [x, y] rest' ACTD (ACTD + ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget
    (by simp [virtualPileTypes_length]; decide)
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, substitute, shift past first block
  rw [applyWord_append, hlift,
      show (x :: y :: rest' : List PileType) = [x] ++ (y :: rest') from rfl,
      virtualPileTypes_append,
      show ACTD + ALIGN.length = (virtualPileTypes ALIGN [x]).length + ACTD from by
        rw [virtualPileTypes_length]; simp; unfold ALIGN; omega,
      applyWord_compile_append_shift, virtualPileTypes_length]
  simp

/-- From CLAUSE_DISQ: penalty propagates (≥ CLAUSE_DISQ on next block). -/
theorem testWord_consumption_disq
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (testWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: rest))) CLAUSE_DISQ ≥
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest)) CLAUSE_DISQ
    := by
  -- 1. Gadget: CLAUSE_DISQ → ≥ CLAUSE_DISQ + m for any word in {POS, NEG, DK}  (activation_correct_disq)
  -- 2. Decompose rest = y :: rest'
  obtain ⟨y, rest', rfl⟩ : ∃ y rest', rest = y :: rest' := by
    match rest, hrest with | y :: rest', _ => exact ⟨y, rest', rfl⟩
  -- Specialize to testWord
  have hgadget : applyWord (testWord i clause)
      (compile (virtualPileTypes ALIGN [x, y])) CLAUSE_DISQ ≥ CLAUSE_DISQ + ALIGN.length := by
    unfold testWord; split <;> exact activation_correct_disq (by simp) x y
  -- 3. Lift to full machine via gadget_lift_ge (window=[x,y], B=rest')
  have hlift := gadget_lift_ge (testWord i clause) [x, y] rest' CLAUSE_DISQ
    (CLAUSE_DISQ + ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, apply mono, shift past first block
  rw [applyWord_append]
  calc ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN (y :: rest'))) CLAUSE_DISQ
      = applyWord suffix (compile (virtualPileTypes ALIGN (x :: y :: rest')))
          (CLAUSE_DISQ + ALIGN.length) := by
        rw [show (x :: y :: rest' : List PileType) = [x] ++ (y :: rest') from rfl,
            virtualPileTypes_append,
            show CLAUSE_DISQ + ALIGN.length = (virtualPileTypes ALIGN [x]).length + CLAUSE_DISQ from by
              rw [virtualPileTypes_length]; simp; decide,
            applyWord_compile_append_shift, virtualPileTypes_length]; simp
    _ ≤ _ := applyWord_mono suffix (virtualPileTypes ALIGN (x :: y :: rest')) hlift

/-- testWord always produces a word from {POS, NEG, DK}. -/
theorem testWord_mem (i : Nat) (clause : Clause) : testWord i clause ∈ [POS, NEG, DK] := by
  unfold testWord; split <;> simp

/-- The activation condition for testWord from NACTD is exactly litMatches. -/
theorem testWord_litMatches (i : Nat) (clause : Clause) (st : PileType) :
    litMatches (clause.getD i .absent) st ↔
    (testWord i clause = POS ∧ st = .Q) ∨ (testWord i clause = NEG ∧ st = .S) := by
  cases h : clause.getD i .absent <;>
    simp_all [litMatches, testWord,
      show POS ≠ NEG from by decide, show NEG ≠ POS from by decide,
      show DK ≠ POS from by decide, show DK ≠ NEG from by decide]

/-- From NACTD: activates (→ ACTD) if literal i matches x, else stays NACTD. -/
theorem testWord_consumption_nactd
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (testWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: rest))) NACTD =
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest))
      (if matchesLiteral x i clause then ACTD else NACTD)
    := by
  -- 1. Gadget: NACTD activation condition is (w=POS∧st=Q)∨(w=NEG∧st=S)  (activation_correct_nactd)
  --    testWord ∈ {POS,NEG,DK}  (testWord_mem)
  --    Bridge: activation condition = litMatches = matchesLiteral  (testWord_litMatches)
  -- 2. Decompose rest = y :: rest'
  obtain ⟨y, rest', rfl⟩ : ∃ y rest', rest = y :: rest' := by
    match rest, hrest with | y :: rest', _ => exact ⟨y, rest', rfl⟩
  -- Specialize to testWord
  have hgadget : applyWord (testWord i clause)
      (compile (virtualPileTypes ALIGN [x, y])) NACTD =
    (if matchesLiteral x i clause then ACTD else NACTD) + ALIGN.length := by
    rw [activation_correct_nactd (testWord_mem i clause) x y]
    simp only [matchesLiteral, testWord_litMatches]
  -- 3. Lift to full machine via gadget_lift_eq (window=[x,y], B=rest')
  have hr : (if matchesLiteral x i clause then ACTD else NACTD) + ALIGN.length <
      (virtualPileTypes ALIGN [x, y]).length := by
    simp [virtualPileTypes_length]; split <;> decide
  have hlift := gadget_lift_eq (testWord i clause) [x, y] rest' NACTD
    ((if matchesLiteral x i clause then ACTD else NACTD) + ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget hr
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, substitute, shift past first block
  rw [applyWord_append, hlift,
      show (x :: y :: rest' : List PileType) = [x] ++ (y :: rest') from rfl,
      virtualPileTypes_append,
      show (if matchesLiteral x i clause then ACTD else NACTD) + ALIGN.length =
        (virtualPileTypes ALIGN [x]).length +
          (if matchesLiteral x i clause then ACTD else NACTD) from by
        rw [virtualPileTypes_length]; simp; omega,
      applyWord_compile_append_shift, virtualPileTypes_length,
      show [x].length = 1 from rfl, Nat.one_mul]

/-- Combined testWord consumption (all three starting states). -/
theorem testWord_consumption
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    let machine := compile (virtualPileTypes ALIGN (x :: rest))
    let suffixMachine := compile (virtualPileTypes ALIGN rest)
    let m := ALIGN.length
    -- from ACTD
    (applyWord (testWord i clause ++ suffix) machine ACTD =
      m + applyWord suffix suffixMachine ACTD)
    -- from CLAUSE_DISQ
    ∧ (applyWord (testWord i clause ++ suffix) machine CLAUSE_DISQ ≥
      m + applyWord suffix suffixMachine CLAUSE_DISQ)
    -- from NACTD
    ∧ (applyWord (testWord i clause ++ suffix) machine NACTD =
      m + applyWord suffix suffixMachine (if matchesLiteral x i clause then ACTD else NACTD))
    :=
  ⟨testWord_consumption_actd i clause suffix x rest hrest,
   testWord_consumption_disq i clause suffix x rest hrest,
   testWord_consumption_nactd i clause suffix x rest hrest⟩

/-- From CLAUSE_DISQ: endTestWord penalty propagates, consuming two blocks. -/
theorem endTestWord_consumption_disq
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x y : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (endTestWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: y :: rest))) CLAUSE_DISQ ≥
    2 * ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest)) CHAIN_DISQ
    := by
  -- 1. Gadget helper: CLAUSE_DISQ → ≥ CHAIN_DISQ + 2*m on three-element machine
  have gadget : ∀ (lp : LitPresence) (st nt1 nt2 : PileType),
      CHAIN_DISQ + 2 * ALIGN.length ≤
        applyWord (match lp with | .pos => ENDPOS | .neg => ENDNEG | .absent => ENDDK)
          (compile (virtualPileTypes ALIGN [st, nt1, nt2])) CLAUSE_DISQ := by decide
  -- 2. Decompose rest = z :: rest'
  obtain ⟨z, rest', rfl⟩ : ∃ z rest', rest = z :: rest' := by
    match rest, hrest with | z :: rest', _ => exact ⟨z, rest', rfl⟩
  -- Specialize to endTestWord
  have hgadget : CHAIN_DISQ + 2 * ALIGN.length ≤
      applyWord (endTestWord i clause)
        (compile (virtualPileTypes ALIGN [x, y, z])) CLAUSE_DISQ := by
    unfold endTestWord; exact gadget (clause.getD i .absent) x y z
  -- 3. Lift to full machine via gadget_lift_ge (window=[x,y,z], B=rest')
  have hlift := gadget_lift_ge (endTestWord i clause) [x, y, z] rest'
    CLAUSE_DISQ (CHAIN_DISQ + 2 * ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, apply mono, shift past two blocks
  rw [applyWord_append]
  calc 2 * ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN (z :: rest'))) CHAIN_DISQ
      = applyWord suffix (compile (virtualPileTypes ALIGN (x :: y :: z :: rest')))
          (CHAIN_DISQ + 2 * ALIGN.length) := by
        rw [show (x :: y :: z :: rest' : List PileType) = [x, y] ++ (z :: rest') from rfl,
            virtualPileTypes_append,
            show CHAIN_DISQ + 2 * ALIGN.length =
              (virtualPileTypes ALIGN [x, y]).length + CHAIN_DISQ from by
              rw [virtualPileTypes_length]; simp; decide,
            applyWord_compile_append_shift, virtualPileTypes_length]; simp
    _ ≤ _ := applyWord_mono suffix (virtualPileTypes ALIGN (x :: y :: z :: rest')) hlift

/-- From ACTD when y = Q: endTestWord reaches END_POS in the next block. -/
theorem endTestWord_consumption_actd_good
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (endTestWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: PileType.Q :: rest))) ACTD =
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: rest))) END_POS
    := by
  -- 1. Gadget helper: ACTD → END_POS + m on [st, Q, nt2]
  have gadget : ∀ (lp : LitPresence) (st nt2 : PileType),
      applyWord (match lp with | .pos => ENDPOS | .neg => ENDNEG | .absent => ENDDK)
        (compile (virtualPileTypes ALIGN [st, PileType.Q, nt2])) ACTD =
      END_POS + ALIGN.length := by decide
  -- 2. Decompose rest = z :: rest'
  obtain ⟨z, rest', rfl⟩ : ∃ z rest', rest = z :: rest' := by
    match rest, hrest with | z :: rest', _ => exact ⟨z, rest', rfl⟩
  -- Specialize to endTestWord
  have hgadget : applyWord (endTestWord i clause)
      (compile (virtualPileTypes ALIGN [x, PileType.Q, z])) ACTD =
    END_POS + ALIGN.length := by
    unfold endTestWord; exact gadget (clause.getD i .absent) x z
  -- 3. Lift to full machine via gadget_lift_eq (window=[x,Q,z], B=rest')
  have hlift := gadget_lift_eq (endTestWord i clause) [x, PileType.Q, z] rest'
    ACTD (END_POS + ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget
    (by simp [virtualPileTypes_length]; decide)
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, substitute, shift past one block
  rw [applyWord_append, hlift,
      show (x :: PileType.Q :: z :: rest' : List PileType) = [x] ++ (PileType.Q :: z :: rest') from rfl,
      virtualPileTypes_append,
      show END_POS + ALIGN.length = (virtualPileTypes ALIGN [x]).length + END_POS from by
        rw [virtualPileTypes_length]; simp; decide,
      applyWord_compile_append_shift, virtualPileTypes_length]; simp

/-- From ACTD when y ≠ Q: endTestWord reaches penalty zone. -/
theorem endTestWord_consumption_actd_bad
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x y : PileType) (rest : List PileType) (hrest : rest ≠ [])
    (hy : y ≠ PileType.Q) :
    applyWord (endTestWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: y :: rest))) ACTD ≥
    2 * ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest)) CHAIN_DISQ
    := by
  -- y ≠ Q means y = S
  have hy : y = PileType.S := by cases y <;> simp_all
  subst hy
  -- 1. Gadget helper: ACTD → ≥ CHAIN_DISQ + 2*m on [st, S, nt2]
  have gadget : ∀ (lp : LitPresence) (st nt2 : PileType),
      CHAIN_DISQ + 2 * ALIGN.length ≤
        applyWord (match lp with | .pos => ENDPOS | .neg => ENDNEG | .absent => ENDDK)
          (compile (virtualPileTypes ALIGN [st, PileType.S, nt2])) ACTD := by decide
  -- 2. Decompose rest = z :: rest'
  obtain ⟨z, rest', rfl⟩ : ∃ z rest', rest = z :: rest' := by
    match rest, hrest with | z :: rest', _ => exact ⟨z, rest', rfl⟩
  -- Specialize to endTestWord
  have hgadget : CHAIN_DISQ + 2 * ALIGN.length ≤
      applyWord (endTestWord i clause)
        (compile (virtualPileTypes ALIGN [x, PileType.S, z])) ACTD := by
    unfold endTestWord; exact gadget (clause.getD i .absent) x z
  -- 3. Lift via gadget_lift_ge (window=[x,S,z], B=rest')
  have hlift := gadget_lift_ge (endTestWord i clause) [x, PileType.S, z] rest'
    ACTD (CHAIN_DISQ + 2 * ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, apply mono, shift past two blocks
  rw [applyWord_append]
  calc 2 * ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN (z :: rest'))) CHAIN_DISQ
      = applyWord suffix (compile (virtualPileTypes ALIGN (x :: PileType.S :: z :: rest')))
          (CHAIN_DISQ + 2 * ALIGN.length) := by
        rw [show (x :: PileType.S :: z :: rest' : List PileType) = [x, PileType.S] ++ (z :: rest') from rfl,
            virtualPileTypes_append,
            show CHAIN_DISQ + 2 * ALIGN.length =
              (virtualPileTypes ALIGN [x, PileType.S]).length + CHAIN_DISQ from by
              rw [virtualPileTypes_length]; simp; decide,
            applyWord_compile_append_shift, virtualPileTypes_length]; simp
    _ ≤ _ := applyWord_mono suffix (virtualPileTypes ALIGN (x :: PileType.S :: z :: rest')) hlift

/-- From NACTD when y = Q and literal matches: endTestWord reaches END_POS. -/
theorem endTestWord_consumption_nactd_good
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ [])
    (hlit : matchesLiteral x i clause) :
    applyWord (endTestWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: PileType.Q :: rest))) NACTD =
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN (PileType.Q :: rest))) END_POS
    := by
  -- 1. Gadget helper: when litMatches, NACTD → END_POS + m on [st, Q, nt2]
  have gadget : ∀ (lp : LitPresence) (st nt2 : PileType),
      if litMatches lp st then
        applyWord (match lp with | .pos => ENDPOS | .neg => ENDNEG | .absent => ENDDK)
          (compile (virtualPileTypes ALIGN [st, PileType.Q, nt2])) NACTD =
        END_POS + ALIGN.length
      else True := by decide
  -- 2. Decompose rest = z :: rest'
  obtain ⟨z, rest', rfl⟩ : ∃ z rest', rest = z :: rest' := by
    match rest, hrest with | z :: rest', _ => exact ⟨z, rest', rfl⟩
  -- Specialize to endTestWord, using matchesLiteral hypothesis
  have hgadget : applyWord (endTestWord i clause)
      (compile (virtualPileTypes ALIGN [x, PileType.Q, z])) NACTD =
    END_POS + ALIGN.length := by
    have hg := gadget (clause.getD i .absent) x z
    rw [if_pos (show litMatches (clause.getD i .absent) x from hlit)] at hg
    unfold endTestWord; exact hg
  -- 3. Lift to full machine via gadget_lift_eq (window=[x,Q,z], B=rest')
  have hlift := gadget_lift_eq (endTestWord i clause) [x, PileType.Q, z] rest'
    NACTD (END_POS + ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget
    (by simp [virtualPileTypes_length]; decide)
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, substitute, shift past one block
  rw [applyWord_append, hlift,
      show (x :: PileType.Q :: z :: rest' : List PileType) = [x] ++ (PileType.Q :: z :: rest') from rfl,
      virtualPileTypes_append,
      show END_POS + ALIGN.length = (virtualPileTypes ALIGN [x]).length + END_POS from by
        rw [virtualPileTypes_length]; simp; decide,
      applyWord_compile_append_shift, virtualPileTypes_length]; simp

/-- From NACTD when y = Q and literal doesn't match: endTestWord reaches penalty zone. -/
theorem endTestWord_consumption_nactd_bad
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ [])
    (hlit : ¬matchesLiteral x i clause) :
    applyWord (endTestWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: PileType.Q :: rest))) NACTD ≥
    2 * ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest)) CHAIN_DISQ
    := by
  -- 1. Gadget helper: when ¬litMatches, NACTD → ≥ CHAIN_DISQ + 2*m on [st, Q, nt2]
  have gadget : ∀ (lp : LitPresence) (st nt2 : PileType),
      if litMatches lp st then True
      else CHAIN_DISQ + 2 * ALIGN.length ≤
        applyWord (match lp with | .pos => ENDPOS | .neg => ENDNEG | .absent => ENDDK)
          (compile (virtualPileTypes ALIGN [st, PileType.Q, nt2])) NACTD := by decide
  -- 2. Decompose rest = z :: rest'
  obtain ⟨z, rest', rfl⟩ : ∃ z rest', rest = z :: rest' := by
    match rest, hrest with | z :: rest', _ => exact ⟨z, rest', rfl⟩
  -- Specialize to endTestWord, using ¬matchesLiteral hypothesis
  have hgadget : CHAIN_DISQ + 2 * ALIGN.length ≤
      applyWord (endTestWord i clause)
        (compile (virtualPileTypes ALIGN [x, PileType.Q, z])) NACTD := by
    have hg := gadget (clause.getD i .absent) x z
    rw [if_neg (show ¬litMatches (clause.getD i .absent) x from hlit)] at hg
    unfold endTestWord; exact hg
  -- 3. Lift via gadget_lift_ge (window=[x,Q,z], B=rest')
  have hlift := gadget_lift_ge (endTestWord i clause) [x, PileType.Q, z] rest'
    NACTD (CHAIN_DISQ + 2 * ALIGN.length)
    (by simp [virtualPileTypes_length]; decide)
    hgadget
  simp only [List.cons_append, List.nil_append] at hlift
  -- 4. Split word ++ suffix, apply mono, shift past two blocks
  rw [applyWord_append]
  calc 2 * ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN (z :: rest'))) CHAIN_DISQ
      = applyWord suffix (compile (virtualPileTypes ALIGN (x :: PileType.Q :: z :: rest')))
          (CHAIN_DISQ + 2 * ALIGN.length) := by
        rw [show (x :: PileType.Q :: z :: rest' : List PileType) = [x, PileType.Q] ++ (z :: rest') from rfl,
            virtualPileTypes_append,
            show CHAIN_DISQ + 2 * ALIGN.length =
              (virtualPileTypes ALIGN [x, PileType.Q]).length + CHAIN_DISQ from by
              rw [virtualPileTypes_length]; simp; decide,
            applyWord_compile_append_shift, virtualPileTypes_length]; simp
    _ ≤ _ := applyWord_mono suffix (virtualPileTypes ALIGN (x :: PileType.Q :: z :: rest')) hlift

/-- Combined endTestWord consumption. -/
theorem endTestWord_consumption
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x y : PileType) (rest : List PileType)
    (hrest : rest ≠ [])
    :
    let m := ALIGN.length
    let machine := compile (virtualPileTypes ALIGN (x :: y :: rest))
    let nextGood := m + applyWord suffix (compile (virtualPileTypes ALIGN (y :: rest))) END_POS
    let nextBad := 2 * m + applyWord suffix (compile (virtualPileTypes ALIGN rest)) CHAIN_DISQ
    (applyWord (endTestWord i clause ++ suffix) machine CLAUSE_DISQ >= nextBad)
    ∧
    (if y = .Q then
      (applyWord (endTestWord i clause ++ suffix) machine ACTD = nextGood) ∧
      if matchesLiteral x i clause then
         applyWord (endTestWord i clause ++ suffix) machine NACTD = nextGood
      else
         applyWord (endTestWord i clause ++ suffix) machine NACTD >= nextBad
    else
      applyWord (endTestWord i clause ++ suffix) machine ACTD >= nextBad
      -- NACTD case is subsumed by ACTD since NACTD is closer to the end than ACTD
    )
    := by
  simp only []
  refine ⟨endTestWord_consumption_disq i clause suffix x y rest hrest, ?_⟩
  by_cases hy : y = PileType.Q
  · subst hy; rw [if_pos rfl]
    refine ⟨endTestWord_consumption_actd_good i clause suffix x rest hrest, ?_⟩
    by_cases hlit : matchesLiteral x i clause
    · rw [if_pos hlit]; exact endTestWord_consumption_nactd_good i clause suffix x rest hrest hlit
    · rw [if_neg hlit]; exact endTestWord_consumption_nactd_bad i clause suffix x rest hrest hlit
  · rw [if_neg hy]; exact endTestWord_consumption_actd_bad i clause suffix x y rest hrest hy
