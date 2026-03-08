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

theorem start_clause_correct :
    -- pile_type = Q, start_pos = START_POS → end_pos = NACTD
    (applyWord START_CLAUSE (compile (virtualPileTypes ALIGN [PileType.Q])) START_POS = NACTD) ∧
    -- pile_type = Q, start_pos = CHAIN_DISQ → end_pos ≥ CLAUSE_DISQ
    (applyWord START_CLAUSE (compile (virtualPileTypes ALIGN [PileType.Q])) CHAIN_DISQ ≥ CLAUSE_DISQ) ∧
    -- pile_type = S, start_pos = START_POS → end_pos = NACTD
    (applyWord START_CLAUSE (compile (virtualPileTypes ALIGN [PileType.S])) START_POS = NACTD) ∧
    -- pile_type = S, start_pos = CHAIN_DISQ → end_pos ≥ CLAUSE_DISQ
    (applyWord START_CLAUSE (compile (virtualPileTypes ALIGN [PileType.S])) CHAIN_DISQ ≥ CLAUSE_DISQ)
  := by decide

/-- Lifted START_CLAUSE from START_POS: on any machine t :: B, reaches NACTD. -/
theorem start_clause_lifted_eq (t : PileType) (B : List PileType) :
    applyWord START_CLAUSE (compile (virtualPileTypes ALIGN (t :: B))) START_POS = NACTD := by
  cases t <;> exact gadget_lift_eq START_CLAUSE [] [_] B START_POS NACTD (by decide) (by decide) (by decide)

/-- Lifted START_CLAUSE from CHAIN_DISQ: on any machine t :: B, reaches ≥ CLAUSE_DISQ. -/
theorem start_clause_lifted_ge (t : PileType) (B : List PileType) :
    CLAUSE_DISQ ≤
      applyWord START_CLAUSE (compile (virtualPileTypes ALIGN (t :: B))) CHAIN_DISQ := by
  cases t <;> exact gadget_lift_ge START_CLAUSE [] [_] B CHAIN_DISQ CLAUSE_DISQ (by decide) (by decide)

/-- START_CLAUSE ++ suffix from CHAIN_DISQ: result ≥ suffix from CLAUSE_DISQ on the same machine. -/
theorem start_clause_disq (suffix : List Action) (t : PileType) (rest : List PileType) :
    applyWord (START_CLAUSE ++ suffix) (compile (virtualPileTypes ALIGN (t :: rest))) CHAIN_DISQ ≥
      applyWord suffix (compile (virtualPileTypes ALIGN (t :: rest))) CLAUSE_DISQ := by
  rw [applyWord_append]
  exact applyWord_mono suffix _ (start_clause_lifted_ge t rest)

/-- START_CLAUSE ++ suffix from START_POS: result = suffix from NACTD on the same machine. -/
theorem start_clause_start (suffix : List Action) (t : PileType) (rest : List PileType) :
    applyWord (START_CLAUSE ++ suffix) (compile (virtualPileTypes ALIGN (t :: rest))) START_POS =
      applyWord suffix (compile (virtualPileTypes ALIGN (t :: rest))) NACTD := by
  rw [applyWord_append, start_clause_lifted_eq]
