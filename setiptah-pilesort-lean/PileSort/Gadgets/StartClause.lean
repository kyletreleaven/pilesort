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
