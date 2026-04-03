/-
  Legacy index-form testChain lemmas, retained for experimentation.

  The two theorems here (`testChain_actd` and `testChain_nactd_old`) are the
  index-based counterparts of `testChain_actd_cons` and `testChain_nactd_cons`
  in TestChain.lean.  They are not on the proof path of `formulaWord_correct`
  and are candidates for deletion once the index-vs-destructured question
  (see plan.md) is resolved.
-/
import PileSort.Mono
import PileSort.Reduction
import PileSort.Reduction.SATToMatchingChain.Gadgets.StartClause
import PileSort.TestConsume
import PileSort.TestChain
import PileSort.ClauseWordNew


/-- ACTD is a trap: from ACTD, testWords stay at exactly ACTD after shifting.
    Mirrors testChain_disq but uses the ACTD equality case. -/
theorem testChain_actd : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType), k < types.length →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) ACTD =
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) ACTD
  | 0, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have htw := testWord_consumption_actd start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest
    have hih := testChain_actd k (start + 1) clause suffix rest (by omega)
    show _ = (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) ACTD
    rw [Nat.succ_mul, htw, hih]; omega

/-- NACTD with no matching literals: stays at exactly NACTD after shifting.
    Mirrors testChain_actd but uses the NACTD case with ¬matchesLiteral. -/
theorem testChain_nactd_old : ∀ (k : Nat) (start : Nat) (clause : Clause)
    (suffix : List Action) (types : List PileType) (hlen : k < types.length),
    (∀ i (hi : i < k), ¬matchesLiteral (types[i]'(by omega)) (start + i) clause) →
    applyWord ((List.range' start k).flatMap (fun i => testWord i clause) ++ suffix)
      (compile (virtualPileTypes ALIGN types)) NACTD =
    k * ALIGN.length +
      applyWord suffix (compile (virtualPileTypes ALIGN (types.drop k))) NACTD
  | 0, _, _, _, _, _, _ => by simp
  | k + 1, start, clause, suffix, [], htypes, _ => by simp at htypes
  | k + 1, start, clause, suffix, x :: rest, htypes, hno => by
    simp only [List.length_cons] at htypes
    have hrest : rest ≠ [] := by intro h; subst h; simp at htypes
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc]
    have hno0 : ¬matchesLiteral x start clause := by
      have := hno 0 (by omega); simp at this; exact this
    have htw := testWord_consumption_nactd start clause
      ((List.range' (start + 1) k).flatMap (fun i => testWord i clause) ++ suffix)
      x rest hrest
    rw [if_neg hno0] at htw
    have hih := testChain_nactd_old k (start + 1) clause suffix rest (by omega) (by
      intro i hi
      have := hno (i + 1) (by omega)
      simp only [List.length_cons, List.getElem_cons_succ] at this
      rw [show start + (i + 1) = start + 1 + i from by omega] at this
      exact this)
    show _ = (k + 1) * ALIGN.length + applyWord suffix
      (compile (virtualPileTypes ALIGN (List.drop k rest))) NACTD
    rw [Nat.succ_mul, htw, hih]; omega
