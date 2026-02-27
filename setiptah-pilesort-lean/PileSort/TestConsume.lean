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
import PileSort.Gadgets.StartClause

def matchesLiteral (x: PileType) (i : Nat) (clause: Clause): Prop :=
  (clause.getD i .absent = .pos ∧ x = .Q) ∨ (clause.getD i .absent = .neg ∧ x = .S)

instance (x: PileType) (i : Nat) (clause: Clause) : Decidable (matchesLiteral x i clause) := by
  unfold matchesLiteral; infer_instance

/-- From ACTD: testWord stays activated, shifting by one block. -/
theorem testWord_consumption_actd
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (testWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: rest))) ACTD =
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest)) ACTD
    := by sorry

/-- From CLAUSE_DISQ: penalty propagates (≥ CLAUSE_DISQ on next block). -/
theorem testWord_consumption_disq
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (testWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: rest))) CLAUSE_DISQ ≥
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest)) CLAUSE_DISQ
    := by sorry

/-- From NACTD: activates (→ ACTD) if literal i matches x, else stays NACTD. -/
theorem testWord_consumption_nactd
    (i : Nat) (clause : Clause) (suffix : List Action)
    (x : PileType) (rest : List PileType) (hrest : rest ≠ []) :
    applyWord (testWord i clause ++ suffix)
      (compile (virtualPileTypes ALIGN (x :: rest))) NACTD =
    ALIGN.length + applyWord suffix (compile (virtualPileTypes ALIGN rest))
      (if matchesLiteral x i clause then ACTD else NACTD)
    := by sorry

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
    := by sorry
