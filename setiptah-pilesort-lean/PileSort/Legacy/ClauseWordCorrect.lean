import PileSort.ClauseWordCorrect

/-- clauseWord from CHAIN_DISQ: penalty propagates unconditionally.

    English proof:
    Apply clauseWord_chain_consumption (with empty suffix) on A1 ++ A2:
    result ≥ (n+1)*m + CHAIN_DISQ. ∎ -/
theorem clauseWord_chain (n : Nat) (clause : Clause)
    (A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    applyWord (clauseWord n clause) (compile (virtualPileTypes ALIGN (A1 ++ A2))) CHAIN_DISQ ≥
      CHAIN_DISQ + (n + 1) * ALIGN.length := by
  have hcc := clauseWord_chain_consumption n clause [] A1 A2 hn hA1 hA2
  simp only [List.append_nil,
    show applyWord ([] : List Action) (compile (virtualPileTypes ALIGN A2)) CHAIN_DISQ = CHAIN_DISQ
      from rfl] at hcc
  omega

/-- Combined clauseWord correctness, assembling start and chain parts. -/
theorem clauseWord_correct (n : Nat) (clause : Clause)
    (A1 A2 : List PileType)
    (hn : n ≥ 1) (hA1 : A1.length = n + 1) (hA2 : A2 ≠ []) :
    let types := virtualPileTypes ALIGN (A1 ++ A2)
    (∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) START_POS = END_POS + n * ALIGN.length)
    ∧
    (¬ HasMatchingAssignment n A1 (satisfiesClause · clause) →
      applyWord (clauseWord n clause) (compile types) START_POS ≥
        CHAIN_DISQ + (n + 1) * ALIGN.length)
    ∧
    applyWord (clauseWord n clause) (compile types) CHAIN_DISQ ≥
      CHAIN_DISQ + (n + 1) * ALIGN.length :=
  ⟨clauseWord_start_sat n clause A1 A2 hn hA1 hA2,
   clauseWord_start_nonsat n clause A1 A2 hn hA1 hA2,
   clauseWord_chain n clause A1 A2 hn hA1 hA2⟩

/-- clauseWord from START_POS on replicated types: if a matching assignment satisfies the
    clause, reaches END_POS + n * ALIGN.length; otherwise reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct parts 1 and 2 for the List.replicate m .Q form. -/
theorem clauseWord_sat (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    (∀ vars : List Bool, vars.length = n → xs = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars c →
      applyWord (clauseWord n c) (compile types) START_POS =
        END_POS + n * ALIGN.length)
    ∧
    (¬ HasMatchingAssignment n xs (satisfiesClause · c) →
      CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c) (compile types) START_POS) := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := clauseWord_correct n c xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2
  constructor
  · exact hcw.1
  · intro hno
    calc CHAIN_DISQ + xs.length * ALIGN.length
        = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
      _ ≤ _ := hcw.2.1 hno

/-- clauseWord from ≥ CHAIN_DISQ on replicated types always reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct part 3 for the List.replicate m .Q form. -/
theorem clauseWord_penalty (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (s : Nat)
    (hn : n ≥ 1) (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) (hs : CHAIN_DISQ ≤ s) :
    CHAIN_DISQ + xs.length * ALIGN.length ≤
      applyWord (clauseWord n c)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))) s := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN (xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  have hA2 : (List.replicate (m - 1) xs).flatten ≠ [] := by
    have : xs ≠ [] := by intro hx; simp [hx] at hxs_len
    rw [show m - 1 = (m - 2) + 1 from by omega, List.replicate_succ, List.flatten_cons]
    simp [this]
  have hcw := (clauseWord_correct n c xs ((List.replicate (m - 1) xs).flatten) hn hxs_len hA2).2.2
  calc CHAIN_DISQ + xs.length * ALIGN.length
      = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
    _ ≤ applyWord (clauseWord n c) _ CHAIN_DISQ := hcw
    _ ≤ applyWord (clauseWord n c) _ s := applyWord_mono (clauseWord n c) _ hs
