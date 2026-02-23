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

/-- Lifted START_CLAUSE from START_POS: on any machine A ++ [t] ++ B,
    from offset A.length * AL + START_POS, reaches A.length * AL + NACTD.
    Cases on t, then gadget_lift_eq with the decide-proved base case. -/
theorem start_clause_lifted_eq (t : PileType) (A B : List PileType) :
    applyWord START_CLAUSE (compile (virtualPileTypes ALIGN (A ++ [t] ++ B)))
      (A.length * ALIGN.length + START_POS) = A.length * ALIGN.length + NACTD := by
  cases t <;> exact gadget_lift_eq START_CLAUSE A [_] B START_POS NACTD (by decide) (by decide) (by decide)

/-- Lifted START_CLAUSE from CHAIN_DISQ: on any machine A ++ [t] ++ B,
    from offset A.length * AL + CHAIN_DISQ, reaches ≥ A.length * AL + CLAUSE_DISQ.
    Cases on t, then gadget_lift_ge with the decide-proved base case. -/
theorem start_clause_lifted_ge (t : PileType) (A B : List PileType) :
    A.length * ALIGN.length + CLAUSE_DISQ ≤
      applyWord START_CLAUSE (compile (virtualPileTypes ALIGN (A ++ [t] ++ B)))
        (A.length * ALIGN.length + CHAIN_DISQ) := by
  cases t <;> exact gadget_lift_ge START_CLAUSE A [_] B CHAIN_DISQ CLAUSE_DISQ (by decide) (by decide)
