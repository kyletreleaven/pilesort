/-
  Formula-level correctness theorems for the SAT-to-pile-sort reduction.

  Composes gadget theorems (clauseWord_correct) into the full
  formulaWord_correct: acceptance ↔ satisfying assignment.

  ## Proof strategy

  The proof is organized around `formulaState`, a tail-recursive computation
  that mirrors the clause-by-clause structure of `formulaWord`. The key
  connection is `formulaState_eq`: formulaState equals applyWord(formulaWord)
  on types with one vestigial block (clauses_.length + 2 Q-replications).

  Two lemmas about formulaState capture the full behavior:

  1. **formulaState_penalty**: If `start ≥ CHAIN_DISQ`, then formulaState
     ends at `≥ CHAIN_DISQ` (plus accumulated blocks). Each clause's
     clauseWord_correct part 3 keeps the state above CHAIN_DISQ, and
     the block accumulation adds init.length * block on top.

  2. **formulaState_sat**: If `start = START_POS`, then:
     - If all clauses in init are satisfied, the inner start stays at
       START_POS after each clause (clauseWord_correct part 1 + NEXT).
       The last clause then runs from START_POS.
     - If some clause in init is unsatisfied, clauseWord_correct part 2
       bumps the inner start to ≥ CHAIN_DISQ, and formulaState_penalty
       handles the remaining clauses.

  These give formulaWord_correct via formulaState_eq + truncation:
  - Forward: all satisfied → formulaState ends at END_POS + n*ALIGN.length
    in the last block, which is < block, so total < types.length → accepted.
  - Backward: some unsatisfied → formulaState ≥ CHAIN_DISQ + all blocks
    ≥ types.length → truncation gives sink → not accepted.
-/
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

/-- Forward direction: a satisfying assignment implies acceptance. -/
theorem formulaWord_forward (n : Nat) (clauses : List Clause)
    (xs : List PileType) (vars : List Bool)
    (hxs_len : xs.length = n + 1)
    (hn : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesFormula vars clauses)
    (hne : clauses ≠ []) :
    let types := virtualPileTypes
        (virtualPileTypes ALIGN xs)
        (List.replicate clauses.length PileType.Q)
    accepts types (formulaWord n clauses) := by
  sorry

/-- On extended types (one extra block), if no satisfying assignment exists,
    the formulaWord sends state 0 past the original types boundary.
    The vestigial block ensures clauseWord_correct part 3 always has room. -/
theorem formulaWord_penalty_ext (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ (∃ vars : List Bool, vars.length = n
        ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars clauses)) :
    let types_ext := virtualPileTypes ALIGN
        (List.replicate (clauses.length + 1) xs).flatten
    applyWord (formulaWord n clauses) (compile types_ext) 0 ≥
      CHAIN_DISQ + clauses.length * xs.length * ALIGN.length := by
  sorry

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

/-- If all init clauses are satisfied by a matching assignment, formulaState
    accumulates blocks cleanly and the last clause runs from START_POS. -/
theorem formulaState_forward (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause)
    (vars : List Bool)
    (hxs_len : xs.length = n + 1)
    (hvars : vars.length = n)
    (hxs : xs = embedVars vars ++ [PileType.Q])
    (hsat : satisfiesFormula vars clauses_) :
    formulaState n xs clauses_ last START_POS =
      clauses_.length * (xs.length * ALIGN.length) +
      formulaState n xs [] last START_POS := by
  sorry

/-- If no matching assignment satisfies all init clauses, formulaState
    reaches the penalty bound. Uses embedVars_injective in the cons case
    to show that the unique matching vars must fail some clause. -/
theorem formulaState_penalty_start (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ (∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars clauses_)) :
    formulaState n xs clauses_ last START_POS ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  sorry

/-- If the starting state is at or above CHAIN_DISQ, then formulaState
    accumulates at least (clauses_.length + 1) full blocks plus CHAIN_DISQ.

    Proof by induction on clauses_.

    Base case (clauses_ = []): formulaState = applyWord(clauseWord last)(types)(start).
    By clauseWord_correct part 3 (via mono from start ≥ CHAIN_DISQ),
    result ≥ CHAIN_DISQ + block. This is (0 + 1) * block + CHAIN_DISQ. ✓

    Cons case (clauses_ = c :: rest):
    formulaState = block + formulaState(rest, last, mid - block)
    where mid = applyWord(clauseWord c ++ NEXT)(types)(start).
    By clauseWord_correct part 3 + applyWord_ge (NEXT doesn't decrease),
    mid ≥ CHAIN_DISQ + block, so mid - block ≥ CHAIN_DISQ.
    By IH: formulaState(rest, last, mid - block) ≥ (rest.length + 1) * block + CHAIN_DISQ.
    Total: block + (rest.length + 1) * block + CHAIN_DISQ
         = (rest.length + 2) * block + CHAIN_DISQ
         = ((c :: rest).length + 1) * block + CHAIN_DISQ. ✓ -/
theorem formulaState_penalty (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause) (start : Nat)
    (hxs_len : xs.length = n + 1)
    (hstart : CHAIN_DISQ ≤ start) :
    formulaState n xs clauses_ last start ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  induction clauses_ generalizing start with
  | nil =>
    simp only [formulaState, List.length_nil, Nat.zero_add, Nat.one_mul]
    have := clauseWord_penalty n last xs 2 start hxs_len (by omega) hstart
    omega
  | cons c rest ih =>
    unfold formulaState; simp only []
    -- clauseWord c from start ≥ CHAIN_DISQ gives result ≥ CHAIN_DISQ + block
    have h_cw := clauseWord_penalty n c xs ((c :: rest).length + 2) start hxs_len (by omega) hstart
    -- NEXT doesn't decrease, so mid ≥ CHAIN_DISQ + block
    have h_mid : CHAIN_DISQ + xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate ((c :: rest).length + 2) .Q))) start := by
      rw [applyWord_append]
      exact Nat.le_trans h_cw (applyWord_ge NEXT _ _)
    -- mid - block ≥ CHAIN_DISQ
    have h_sub : CHAIN_DISQ ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate ((c :: rest).length + 2) .Q))) start
        - xs.length * ALIGN.length := by omega
    have h_ih := ih _ h_sub
    have h_arith : ((c :: rest).length + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + (rest.length + 1) * (xs.length * ALIGN.length) := by
      simp [List.length_cons, Nat.succ_mul]; omega
    rw [h_arith]
    omega

theorem formulaWord_split (n : Nat) (init : List Clause) (last : Clause) :
    formulaWord n (init ++ [last]) =
    (init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last := by
  unfold formulaWord
  rw [List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← List.append_assoc]
  show ((init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last ++ NEXT).dropLast =
    (init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last
  unfold NEXT
  rw [List.dropLast_concat]

/-- Peeling one Q from the front of a replicated virtualPileTypes. -/
private theorem virtualPileTypes_replicate_Q_cons (inner : List PileType) (m : Nat) :
    virtualPileTypes inner (List.replicate (m + 1) .Q) =
    inner ++ virtualPileTypes inner (List.replicate m .Q) := by
  simp [virtualPileTypes, List.replicate_succ, List.flatMap_cons, applyPile]

/-- Peeling the first clause off a formulaWord. -/
private theorem formulaWord_cons (n : Nat) (c : Clause) (rest : List Clause) (last : Clause) :
    formulaWord n ((c :: rest) ++ [last]) =
    (clauseWord n c ++ NEXT) ++ formulaWord n (rest ++ [last]) := by
  rw [formulaWord_split, formulaWord_split]
  simp [List.flatMap_cons, List.append_assoc]

/-- formulaState_eq: The tail-recursive formulaState computation equals
    the direct application of formulaWord to the compiled machine.

    Given clauses = init ++ [last], the types have (init.length + 2)
    Q-replications of the inner block (virtualPileTypes ALIGN xs):
    - init.length blocks for the remaining clauses in init,
    - 1 block for last,
    - 1 vestigial block (so clauseWord_correct part 3 has room).

    The RHS applies the full formulaWord to a single type list.
    The LHS (formulaState) uses shrinking types at each recursive level.
    The shift lemma bridges these views: after clauseWord c ++ NEXT
    advances past the first block (h_advance), we peel off that block
    and recurse on inner types with the remaining formula word. -/
theorem formulaState_eq (n : Nat) (xs : List PileType)
    (init : List Clause) (last : Clause) (start : Nat)
    (h_advance : ∀ (c : Clause) (m : Nat) (s : Nat), m ≥ 2 →
      xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate m .Q))) s) :
    formulaState n xs init last start =
      applyWord (formulaWord n (init ++ [last]))
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
          (List.replicate (init.length + 2) .Q))) start := by
  induction init generalizing start with
  | nil =>
    -- formulaState unfolds to applyWord (clauseWord n last) (compile types₂) start
    -- formulaWord n [last] = clauseWord n last
    simp only [formulaState]
    have hfw : formulaWord n ([] ++ [last]) = clauseWord n last := by
      rw [formulaWord_split]; simp
    rw [hfw]
  | cons c rest ih =>
    -- Unfold formulaState and apply IH
    unfold formulaState; simp only []
    rw [ih]
    -- Now work from the RHS toward the LHS
    symm
    rw [formulaWord_cons, applyWord_append]
    -- Goal: applyWord fw (compile types_outer) mid = block + applyWord fw (compile types_inner) (mid - block)
    -- Decompose types_outer = vpt ++ types_inner
    have h_types : virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate ((c :: rest).length + 2) .Q) =
      virtualPileTypes ALIGN xs ++
        virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q) := by
      show virtualPileTypes _ (List.replicate (rest.length + 2 + 1) .Q) = _
      rw [virtualPileTypes_replicate_Q_cons]
    rw [h_types]
    -- h_advance: mid ≥ block
    have hmid : xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes ALIGN xs ++
            virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q)))
          start := by
      rw [← h_types]
      exact h_advance c ((c :: rest).length + 2) start (by omega)
    -- Use shift lemma backwards: rewrite RHS to match LHS
    have h_len : (virtualPileTypes ALIGN xs).length = xs.length * ALIGN.length :=
      virtualPileTypes_length ALIGN xs
    have h_shift := applyWord_compile_append_shift
        (formulaWord n (rest ++ [last]))
        (virtualPileTypes ALIGN xs)
        (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q))
        (applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes ALIGN xs ++
            virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q)))
          start - xs.length * ALIGN.length)
    rw [h_len] at h_shift
    rw [← h_shift]
    congr 1
    omega

private theorem replicate_succ_append {α : Type} (m : Nat) (x : α) :
    List.replicate (m + 1) x = List.replicate m x ++ [x] := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (x :: ·) ih

/-- Formula-level correctness: a machine compiled from virtualPileTypes ALIGN xs,
    replicated over m clauses, accepts formulaWord n clauses iff
    xs = embedVars(vars) ++ [Q] for some assignment vars satisfying the formula. -/
theorem formulaWord_correct (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    let types := virtualPileTypes
        (virtualPileTypes ALIGN xs)
        (List.replicate clauses.length PileType.Q)
    accepts types (formulaWord n clauses) ↔
      ∃ vars : List Bool, vars.length = n
        ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars clauses := by
  intro types
  constructor
  · -- Backward: accepts → ∃ satisfying vars (contrapositive via penalty_ext + truncation)
    intro hacc
    exact Classical.byContradiction fun hno => by
      have hpen := formulaWord_penalty_ext n clauses xs hxs_len hno
      -- Rewrite types as virtualPileTypes ALIGN (replicate m xs).flatten
      have htypes : types = virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten :=
        virtualPileTypes_replicate_Q_comp ALIGN xs clauses.length
      -- types_ext = types ++ extra
      have hext : virtualPileTypes ALIGN (List.replicate (clauses.length + 1) xs).flatten =
          virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten ++
          virtualPileTypes ALIGN xs := by
        rw [replicate_succ_append, List.flatten_append, virtualPileTypes_append,
            List.flatten_cons, List.flatten_nil, List.append_nil]
      rw [htypes] at hacc; rw [hext] at hpen
      unfold accepts at hacc
      -- Truncation: result on types = min(result on ext, types.length)
      have htrunc := applyWord_append_truncate (formulaWord n clauses)
          (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten)
          (virtualPileTypes ALIGN xs) 0 (Nat.zero_le _)
      -- types.length ≤ result on ext (since CHAIN_DISQ ≥ 1)
      have hge : (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten).length ≤
          applyWord (formulaWord n clauses) (compile
            (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten ++
             virtualPileTypes ALIGN xs)) 0 := by
        have hlen : (virtualPileTypes ALIGN (List.replicate clauses.length xs).flatten).length =
            clauses.length * xs.length * ALIGN.length := by
          rw [virtualPileTypes_length, flatten_replicate_length, Nat.mul_assoc]
        unfold CHAIN_DISQ at hpen; omega
      rw [htrunc, Nat.min_eq_right hge] at hacc
      omega
  · -- Forward: ∃ satisfying vars → accepts
    intro ⟨vars, hn, hxs, hsat⟩
    exact formulaWord_forward n clauses xs vars hxs_len hn hxs hsat hne
