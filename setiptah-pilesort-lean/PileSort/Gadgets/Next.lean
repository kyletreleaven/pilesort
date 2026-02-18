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
      simp [List.getElem_append_right (by omega : A.length ≤ A.length + s)]
    rw [heq]
    cases B[s] <;> cases act <;> omega
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
  -- NEXT = [.a], so applyWord reduces to a single compile step
  simp only [NEXT, applyWord, List.foldl]
  induction xs generalizing k with
  | nil => omega
  | cons x rest ih =>
    simp only [virtualPileTypes, List.flatMap_cons]
    cases k with
    | zero =>
      -- compile (applyPile x ALIGN ++ ...) .a END_POS
      -- END_POS = 5 < 6 = (applyPile x ALIGN).length, so only first block matters
      -- (applyPile x ALIGN)[5] = S for all x, so compile gives 6
      simp only [Nat.zero_mul, Nat.add_zero]
      cases x <;> native_decide
    | succ k' =>
      -- Shift past first block using compile_append_right, then apply IH
      have hk' : k' < rest.length := by omega
      have hrw : END_POS + (k' + 1) * ALIGN.length =
          (applyPile x ALIGN).length + (END_POS + k' * ALIGN.length) := by
        rw [applyPile_length]; ring
      rw [hrw, compile_append_right]
      rw [applyPile_length]
      have := ih k' hk'
      simp only [virtualPileTypes, List.flatMap_cons] at this
      omega
