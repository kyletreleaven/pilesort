/-
  Proof of NEXT gadget correctness.

  Mirrors test_next from test_words.py:
    For each next_type ∈ {Q, S}:
      Applying NEXT from END_POS on virtual_pile_types(ALIGN, (Q, next_type))
      reaches START_POS + ALIGN.length
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words

theorem next_correct :
    -- next_type = Q
    (applyWord (compile (virtualPileTypes ALIGN [PileType.Q, PileType.Q])) END_POS NEXT
      = START_POS + ALIGN.length) ∧
    -- next_type = S
    (applyWord (compile (virtualPileTypes ALIGN [PileType.Q, PileType.S])) END_POS NEXT
      = START_POS + ALIGN.length)
  := by native_decide
