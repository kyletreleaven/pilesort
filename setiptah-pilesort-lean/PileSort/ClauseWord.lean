
import PileSort.Mono
import PileSort.Reduction
import PileSort.Gadgets.Next

/-- Clause word correctness for machine compiled from virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    where A1 has length n+1. -/
theorem clauseWord_correct (n : Nat) (clause : Clause)
    (A0 A1 A2 : List PileType)
    (hA1 : A1.length = n + 1) :
    let types := virtualPileTypes ALIGN (A0 ++ A1 ++ A2)
    let k := A0.length
    let m := ALIGN.length
    -- From START_POS with satisfying assignment: → END_POS
    (∀ vars : List Bool, vars.length = n → A1 = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars clause →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) =
        END_POS + (k + n) * m)
    ∧
    -- From START_POS without any satisfying assignment matching A1: → penalty
    (¬ (∃ vars : List Bool, vars.length = n ∧ A1 = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars clause) →
      applyWord (clauseWord n clause) (compile types) (START_POS + k * m) ≥
        CHAIN_DISQ + (k + n + 1) * m)
    ∧
    -- From CHAIN_DISQ: penalty propagates unconditionally
    applyWord (clauseWord n clause) (compile types) (CHAIN_DISQ + k * m) ≥
      CHAIN_DISQ + (k + n + 1) * m := by
  sorry

theorem list_split_last {α : Type} : ∀ (l : List α), l ≠ [] →
    ∃ init last, l = init ++ [last] ∧ init.length + 1 = l.length
  | [x], _ => ⟨[], x, rfl, rfl⟩
  | x :: y :: rest, _ => by
    have ⟨init, last, h, hlen⟩ := list_split_last (y :: rest) (by simp)
    exact ⟨x :: init, last, by rw [h]; simp, by simp_all [List.length_cons]⟩

/-- clauseWord from START_POS on replicated types: if a matching assignment satisfies the
    clause, reaches END_POS + n * ALIGN.length; otherwise reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct parts 1 and 2 for the List.replicate m .Q form. -/
theorem clauseWord_sat (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    (∀ vars : List Bool, vars.length = n → xs = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars c →
      applyWord (clauseWord n c) (compile types) START_POS =
        END_POS + n * ALIGN.length)
    ∧
    (¬ (∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars c) →
      CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c) (compile types) START_POS) := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN ([] ++ xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  have hcw := clauseWord_correct n c [] xs ((List.replicate (m - 1) xs).flatten) hxs_len
  simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hcw
  constructor
  · exact hcw.1
  · intro hno
    have := hcw.2.1 hno
    calc CHAIN_DISQ + xs.length * ALIGN.length
        = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
      _ ≤ _ := this

/-- clauseWord ++ NEXT from START_POS on replicated types: if a matching assignment
    satisfies the clause, advances exactly one block; otherwise reaches ≥ CHAIN_DISQ + block.
    Combines clauseWord_sat with next_correct. -/
theorem clauseNext_sat (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat)
    (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q)
    (∀ vars : List Bool, vars.length = n → xs = embedVars vars ++ [PileType.Q] →
      satisfiesClause vars c →
      applyWord (clauseWord n c ++ NEXT) (compile types) START_POS =
        xs.length * ALIGN.length)
    ∧
    (¬ (∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars c) →
      CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT) (compile types) START_POS) := by
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN ([] ++ xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  simp only [List.nil_append] at h_eq
  rw [h_eq]
  have hcw := clauseWord_correct n c [] xs ((List.replicate (m - 1) xs).flatten) hxs_len
  simp only [List.length_nil, Nat.zero_mul, Nat.zero_add, Nat.add_zero, List.nil_append] at hcw
  have hk : n < (xs ++ (List.replicate (m - 1) xs).flatten).length := by
    simp; omega
  constructor
  · intro vars hvars hxs hsat
    rw [applyWord_append, hcw.1 vars hvars hxs hsat]
    have hnext := next_correct (xs ++ (List.replicate (m - 1) xs).flatten) n hk
    simp only [START_POS] at hnext ⊢
    rw [hnext, hxs_len]; omega
  · intro hno
    rw [applyWord_append]
    calc CHAIN_DISQ + xs.length * ALIGN.length
        = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
      _ ≤ applyWord (clauseWord n c) _ START_POS := hcw.2.1 hno
      _ ≤ applyWord NEXT _ _ := applyWord_ge NEXT _ _

/-- clauseWord from ≥ CHAIN_DISQ on replicated types always reaches ≥ CHAIN_DISQ + block.
    Repackages clauseWord_correct part 3 for the List.replicate m .Q form. -/
theorem clauseWord_penalty (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (s : Nat)
    (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) (hs : CHAIN_DISQ ≤ s) :
    CHAIN_DISQ + xs.length * ALIGN.length ≤
      applyWord (clauseWord n c)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))) s := by
  -- Rewrite types to clauseWord_correct form
  have h_eq : virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q) =
      virtualPileTypes ALIGN ([] ++ xs ++ (List.replicate (m - 1) xs).flatten) := by
    rw [virtualPileTypes_replicate_Q_comp]; congr 1
    have : m = (m - 1) + 1 := by omega
    rw [this, List.replicate_succ, List.flatten_cons]; simp
  rw [h_eq]
  -- clauseWord_correct part 3 with A0=[], A1=xs, A2=remaining
  have hcw := (clauseWord_correct n c [] xs ((List.replicate (m - 1) xs).flatten) hxs_len).2.2
  simp only [List.length_nil, Nat.zero_mul, Nat.zero_add] at hcw
  -- mono: result(s) ≥ result(CHAIN_DISQ) ≥ bound
  calc CHAIN_DISQ + xs.length * ALIGN.length
      = CHAIN_DISQ + (n + 1) * ALIGN.length := by rw [hxs_len]
    _ ≤ applyWord (clauseWord n c) _ CHAIN_DISQ := hcw
    _ ≤ applyWord (clauseWord n c) _ s :=
        applyWord_mono (clauseWord n c) _ hs
