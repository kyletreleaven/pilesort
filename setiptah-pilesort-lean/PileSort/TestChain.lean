import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.StartClause
import PileSort.TestConsume

/-- ACTD in consumption form: from ACTD, testWords shift past A1 and stay ACTD. -/
theorem testChain_actd_cons : ∀ (A1 A2 : List PileType)
    (start : Nat) (clause : Clause) (suffix : List Action), A2 ≠ [] →
    applyWord ((List.range' start A1.length).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN (A1 ++ A2))) ACTD =
    A1.length * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN A2)) ACTD
  | [], _, _, _, _, _ => by simp
  | a :: rest, A2, start, clause, suffix, hA2 => by
    show applyWord ((List.range' start (rest.length + 1)).flatMap _ ++ suffix) _ _ = _
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have hrest_ne : rest ++ A2 ≠ [] := by
      cases rest <;> simp [hA2]
    have htw := testWord_consumption_actd start clause
      ((List.range' (start + 1) rest.length).flatMap (fun i => testWord i clause) ++ suffix)
      a (rest ++ A2) hrest_ne
    have hih := testChain_actd_cons rest A2 (start + 1) clause suffix hA2
    simp only [List.cons_append] at htw ⊢
    rw [htw, hih]
    show ALIGN.length + (rest.length * ALIGN.length + _) =
      (rest.length + 1) * ALIGN.length + _
    rw [Nat.add_mul, Nat.one_mul]; omega
