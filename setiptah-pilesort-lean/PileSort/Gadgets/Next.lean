/-
  Proof of NEXT gadget correctness.

  NEXT = [a] advances from END_POS to the start of the next ALIGN block.
  This works because position END_POS in any applyPile block of ALIGN is S,
  and action a on S advances.
-/
import PileSort.Automata
import PileSort.Mono
import PileSort.VirtualPileTypes
import PileSort.Words

/-- Position END_POS in any applyPile block of ALIGN is S.
    This is the key computational fact that makes NEXT work. -/
theorem applyPile_align_endpos (x : PileType) :
    have : END_POS < (applyPile x ALIGN).length := by cases x <;> decide
    (applyPile x ALIGN)[END_POS] = PileType.S := by
  cases x <;> decide

/-- NEXT advances from END_POS + k*m to START_POS + (k+1)*m
    on any machine compiled from virtualPileTypes ALIGN xs,
    provided k < xs.length. -/
theorem next_correct (xs : List PileType) (k : Nat) (hk : k < xs.length) :
    let types := virtualPileTypes ALIGN xs
    let m := ALIGN.length
    applyWord NEXT (compile types) (END_POS + k * m) = START_POS + (k + 1) * m := by
  simp only [NEXT, applyWord, List.foldl]
  -- virtualPileTypes ALIGN (x :: rest) = applyPile x ALIGN ++ virtualPileTypes ALIGN rest
  induction xs generalizing k with
  | nil => simp at hk
  | cons x rest ih =>
    have vpt_cons : virtualPileTypes ALIGN (x :: rest) =
        applyPile x ALIGN ++ virtualPileTypes ALIGN rest := by
      simp [virtualPileTypes]
    rw [vpt_cons]
    cases k with
    | zero =>
      simp only [Nat.zero_mul, Nat.add_zero]
      -- END_POS < block length, so compile_append_left reduces to first block
      have hlt : END_POS < (applyPile x ALIGN).length := by
        rw [applyPile_length]; decide
      rw [compile_append_left _ _ _ _ hlt]
      -- Unfold compile, use applyPile_align_endpos: type at END_POS is S, action a advances
      unfold compile
      rw [dif_pos hlt, applyPile_align_endpos x]
      -- match PileType.S, Action.a reduces to END_POS + 1
      decide
    | succ k' =>
      -- Shift past first block using compile_append_right, then IH
      have hlen : (x :: rest).length = rest.length + 1 := rfl
      have hk' : k' < rest.length := by omega
      have hAL : ALIGN.length = 6 := by decide
      have hEP : END_POS = 5 := by decide
      have hSP : START_POS = 0 := by decide
      have hrw : END_POS + (k' + 1) * ALIGN.length =
          (applyPile x ALIGN).length + (END_POS + k' * ALIGN.length) := by
        rw [applyPile_length, hAL, hEP]; omega
      rw [hrw, compile_append_right, applyPile_length, ih k' hk']
      rw [hAL, hSP]; omega
