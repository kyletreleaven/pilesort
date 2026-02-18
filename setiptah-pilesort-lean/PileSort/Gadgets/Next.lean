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

/-- applyPile preserves the length of the pile type list. -/
theorem applyPile_length (t : PileType) (pt : List PileType) :
    (applyPile t pt).length = pt.length := by
  cases t <;> simp [applyPile, applyStack]

/-- compile on a concatenation at a position in the right part
    equals the left length plus compile on the right part. -/
theorem compile_append_right (A B : List PileType) (act : Action) (s : Nat) :
    compile (A ++ B) act (A.length + s) = A.length + compile B act s := by
  unfold compile
  by_cases hs : s < B.length
  · -- Both sides enter the "in bounds" branch
    have h1 : A.length + s < (A ++ B).length := by simp; omega
    rw [dif_pos h1, dif_pos hs]
    have heq : (A ++ B)[A.length + s] = B[s] := by
      rw [List.getElem_append_right (by omega : A.length ≤ A.length + s)]
      congr 1; omega
    rw [heq]
    split <;> omega
  · -- Both sides enter the "out of bounds" branch
    have h1 : ¬(A.length + s < (A ++ B).length) := by simp; omega
    rw [dif_neg h1, dif_neg hs]

/-- NEXT advances from END_POS + k*m to START_POS + (k+1)*m
    on any machine compiled from virtualPileTypes ALIGN xs,
    provided k < xs.length. -/
theorem next_correct (xs : List PileType) (k : Nat) (hk : k < xs.length) :
    let types := virtualPileTypes ALIGN xs
    let m := ALIGN.length
    applyWord NEXT (compile types) (END_POS + k * m) = START_POS + (k + 1) * m := by
  sorry
