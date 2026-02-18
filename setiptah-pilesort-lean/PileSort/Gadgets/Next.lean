/-
  Proof of NEXT gadget correctness.

  NEXT = [a] advances from END_POS to the start of the next ALIGN block.
  This works because ALIGN[END_POS] = S and action a on S advances.
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words

-- Base case (original test_next): verified by decide
theorem next_correct_base :
    -- next_type = Q
    (applyWord NEXT (compile (virtualPileTypes ALIGN [PileType.Q, PileType.Q])) END_POS
      = START_POS + ALIGN.length) ∧
    -- next_type = S
    (applyWord NEXT (compile (virtualPileTypes ALIGN [PileType.Q, PileType.S])) END_POS
      = START_POS + ALIGN.length)
  := by decide

/-- NEXT advances from END_POS + k*m to START_POS + (k+1)*m
    on any machine compiled from virtualPileTypes ALIGN xs,
    provided k < xs.length. -/
theorem next_correct (xs : List PileType) (k : Nat) (hk : k < xs.length) :
    let types := virtualPileTypes ALIGN xs
    let m := ALIGN.length
    applyWord NEXT (compile types) (END_POS + k * m) = START_POS + (k + 1) * m := by
  sorry
