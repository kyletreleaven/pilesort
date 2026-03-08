/-
  Proof of START_CLAUSE gadget correctness.

  Mirrors test_start_clause from test_words.py:
    For each pile_type ∈ {Q, S} and start_pos ∈ {START_POS, CHAIN_DISQ}:
      - From START_POS: applying START_CLAUSE reaches NACTD
      - From CHAIN_DISQ: applying START_CLAUSE reaches a position ≥ CLAUSE_DISQ
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words
import PileSort.Gadgets.Lifting

/-- From START_POS, START_CLAUSE reaches NACTD for any pile type. -/
theorem start_clause_correct_start (t : PileType) :
    applyWord START_CLAUSE (compile (virtualPileTypes ALIGN [t])) START_POS = NACTD := by
  revert t; decide

/-- From CHAIN_DISQ, START_CLAUSE reaches ≥ CLAUSE_DISQ for any pile type. -/
theorem start_clause_correct_disq (t : PileType) :
    CLAUSE_DISQ ≤ applyWord START_CLAUSE (compile (virtualPileTypes ALIGN [t])) CHAIN_DISQ := by
  revert t; decide

/-- START_CLAUSE ++ suffix from CHAIN_DISQ: result ≥ suffix from CLAUSE_DISQ on the same machine. -/
theorem start_clause_disq (suffix : List Action) (t : PileType) (rest : List PileType) :
    applyWord (START_CLAUSE ++ suffix) (compile (virtualPileTypes ALIGN (t :: rest))) CHAIN_DISQ ≥
      applyWord suffix (compile (virtualPileTypes ALIGN (t :: rest))) CLAUSE_DISQ := by
  rw [applyWord_append]
  have h := gadget_lift_ge START_CLAUSE [t] rest CHAIN_DISQ CLAUSE_DISQ
    (by simp [virtualPileTypes_length]; decide)
    (start_clause_correct_disq t)
  simp only [List.singleton_append] at h
  exact applyWord_mono suffix _ h

/-- START_CLAUSE ++ suffix from START_POS: result = suffix from NACTD on the same machine. -/
theorem start_clause_start (suffix : List Action) (t : PileType) (rest : List PileType) :
    applyWord (START_CLAUSE ++ suffix) (compile (virtualPileTypes ALIGN (t :: rest))) START_POS =
      applyWord suffix (compile (virtualPileTypes ALIGN (t :: rest))) NACTD := by
  rw [applyWord_append]
  have h := gadget_lift_eq START_CLAUSE [t] rest START_POS NACTD
    (by simp [virtualPileTypes_length]; decide)
    (start_clause_correct_start t)
    (by simp [virtualPileTypes_length]; decide)
  simp only [List.singleton_append] at h
  rw [h]
