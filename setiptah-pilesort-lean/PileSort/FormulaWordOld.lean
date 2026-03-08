import PileSort.Mono
import PileSort.Reduction
import PileSort.ClauseWord
import PileSort.ClauseWordCorrect
import PileSort.Gadgets.Next
import PileSort.FormulaWordNew

/-- ADAPTER: next_correct in replicated form. -/
theorem next_correct_rep (n : Nat) (xs : List PileType)
    (m : Nat)
    (hxs_len : xs.length = n + 1) (hm : m ≥ 2) :
    applyWord NEXT
      (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)))
      (END_POS + n * ALIGN.length) = START_POS + xs.length * ALIGN.length := by
  have h_split : (List.replicate m xs).flatten =
      xs ++ (List.replicate (m - 1) xs).flatten := by
    match m, hm with
    | m' + 2, _ => simp [List.replicate_succ, List.flatten_cons]
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp, h_split]
  rw [h_eq]
  have hk : n < (xs ++ (List.replicate (m - 1) xs).flatten).length := by simp; omega
  rw [next_correct (xs ++ (List.replicate (m - 1) xs).flatten) n hk, hxs_len]

/-- Peeling one Q from the front of a replicated virtualPileTypes. -/
private theorem virtualPileTypes_replicate_Q_cons' (inner : List PileType) (m : Nat) :
    virtualPileTypes inner (List.replicate (m + 1) .Q) =
    inner ++ virtualPileTypes inner (List.replicate m .Q) := by
  simp [virtualPileTypes, List.replicate_succ, List.flatMap_cons, applyPile]
