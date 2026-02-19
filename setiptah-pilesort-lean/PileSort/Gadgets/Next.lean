/-
  Proof of NEXT gadget correctness.

  NEXT = [a] advances from END_POS to the start of the next ALIGN block.
  This works because position END_POS in any applyPile block of ALIGN is S,
  and action a on S advances.
-/
import PileSort.Automata
import PileSort.VirtualPileTypes
import PileSort.Words

/-- Position END_POS in any applyPile block of ALIGN is S. -/
theorem applyPile_align_endpos (x : PileType) :
    have : END_POS < (applyPile x ALIGN).length := by cases x <;> decide
    (applyPile x ALIGN)[END_POS] = PileType.S := by
  cases x <;> decide

/-- NEXT advances from END_POS + k*m to START_POS + (k+1)*m. -/
theorem next_correct (xs : List PileType) (k : Nat) (hk : k < xs.length) :
    let types := virtualPileTypes ALIGN xs
    let m := ALIGN.length
    applyWord NEXT (compile types) (END_POS + k * m) = START_POS + (k + 1) * m := by
  simp only [NEXT, applyWord, List.foldl]
  have hj : END_POS < ALIGN.length := by decide
  have hAL : ALIGN.length = 6 := by decide
  have hEP : END_POS = 5 := by decide
  have hSP : START_POS = 0 := by decide
  -- 1. The type at position END_POS + k*m is S
  have hbound : END_POS + k * ALIGN.length < (virtualPileTypes ALIGN xs).length := by
    rw [virtualPileTypes_length, hAL, hEP]; omega
  have htype : (virtualPileTypes ALIGN xs)[END_POS + k * ALIGN.length] = PileType.S := by
    simp only [show END_POS + k * ALIGN.length = k * ALIGN.length + END_POS from by omega,
               virtualPileTypes_getElem ALIGN xs k END_POS hk hj, applyPile_align_endpos]
  -- 2. compile with type S and action a gives END_POS + k*m + 1 = START_POS + (k+1)*m
  unfold compile; rw [dif_pos hbound, htype]; simp [hAL, hEP, hSP]; omega
