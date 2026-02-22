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
import PileSort.ClauseWord
import PileSort.Gadgets.Next

/-- If all init clauses are satisfied by a matching assignment, formulaState
    accumulates blocks cleanly and the last clause runs from START_POS.

    By induction on clauses_.
    Base: trivial (0 * block + ...).
    Cons (c :: rest): satisfiesFormula gives satisfiesClause vars c and
    satisfiesFormula vars rest. clauseNext_sat part 1 gives mid = block,
    so mid - block = 0 = START_POS. IH gives the rest. -/
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
  induction clauses_ with
  | nil => simp [formulaState]
  | cons c rest ih =>
    have hsat_c : satisfiesClause vars c := hsat c (List.mem_cons_self c rest)
    have hsat_rest : satisfiesFormula vars rest :=
      fun cl hmem => hsat cl (List.mem_cons_of_mem c hmem)
    have h_mid := (clauseNext_sat n c xs ((c :: rest).length + 2) hxs_len (by omega)).1
      vars hvars hxs hsat_c
    show xs.length * ALIGN.length + formulaState n xs rest last
        (applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
            (List.replicate ((c :: rest).length + 2) .Q))) START_POS
         - xs.length * ALIGN.length) =
      (c :: rest).length * (xs.length * ALIGN.length) + formulaState n xs [] last START_POS
    rw [h_mid, show xs.length * ALIGN.length - xs.length * ALIGN.length = START_POS from by
      unfold START_POS; omega]
    rw [ih hsat_rest]
    simp [List.length_cons, Nat.succ_mul]; omega

/-- If no assignment satisfies c :: rest but some assignment satisfies c,
    then no assignment satisfies rest (since xs determines vars uniquely
    via embedVars_injective). -/
theorem not_satisfiesFormula_rest (n : Nat) (xs : List PileType)
    (c : Clause) (rest : List Clause)
    (hno : ¬ (∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars (c :: rest)))
    (hc : ∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars c) :
    ¬ (∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars rest) := by
  obtain ⟨vars₀, hvars₀, hxs₀, hsat₀⟩ := hc
  intro ⟨vars', hvars', hxs', hsat'⟩
  have heq : vars' = vars₀ := by
    have : embedVars vars' = embedVars vars₀ := by
      have := hxs₀ ▸ hxs'; simp at this; exact this.symm
    exact embedVars_injective vars' vars₀ this
  subst heq
  exact hno ⟨vars', hvars', hxs', fun cl hmem => by
    cases List.mem_cons.mp hmem with
    | inl h => exact h ▸ hsat₀
    | inr h => exact hsat' cl h⟩

/-- clauseWord ++ NEXT always advances at least one block from any starting state.
    If s = 0 = START_POS: clauseNext_sat gives ≥ block.
    If s ≥ 1 = CHAIN_DISQ: clauseWord_penalty + applyWord_ge gives ≥ CHAIN_DISQ + block > block. -/
theorem clauseNext_advance (n : Nat) (c : Clause) (xs : List PileType)
    (m : Nat) (s : Nat)
    (hxs_len : xs.length = n + 1)
    (hm : m ≥ 2) :
    xs.length * ALIGN.length ≤
      applyWord (clauseWord n c ++ NEXT)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate m .Q))) s := by
  by_cases hs : s = 0
  · -- s = 0 = START_POS
    subst hs
    have h := clauseNext_sat n c xs m hxs_len hm
    rcases Classical.em (∃ vars, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars c) with ⟨vars, hvars, hxs, hsat⟩ | hnc
    · have := h.1 vars hvars hxs hsat; unfold START_POS at this; omega
    · have := h.2 hnc; unfold START_POS at this; omega
  · -- s ≥ 1 = CHAIN_DISQ
    have : CHAIN_DISQ ≤ s := by unfold CHAIN_DISQ; omega
    have h_cw := clauseWord_penalty n c xs m s hxs_len hm this
    rw [applyWord_append]
    calc xs.length * ALIGN.length
        ≤ CHAIN_DISQ + xs.length * ALIGN.length := by omega
      _ ≤ applyWord (clauseWord n c) _ s := h_cw
      _ ≤ applyWord NEXT _ _ := applyWord_ge NEXT _ _

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

/-- If no matching assignment satisfies all init clauses, formulaState
    reaches the penalty bound.

    By induction on clauses_. Base case: clauseWord_sat part 2.
    Cons case: clauseNext_sat gives mid, then either
    formulaState_penalty (if ¬∃ satisfying c) or
    IH via not_satisfiesFormula_rest (if ∃ satisfying c). -/
theorem formulaState_penalty_start (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ (∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars clauses_)) :
    formulaState n xs clauses_ last START_POS ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  induction clauses_ with
  | nil =>
    simp only [formulaState, List.length_nil, Nat.zero_add, Nat.one_mul]
    have hno' : ¬ (∃ vars, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars last) :=
      fun ⟨vars, hvars, hxs, _⟩ => hno ⟨vars, hvars, hxs, fun _ h => absurd h (List.not_mem_nil _)⟩
    have := (clauseWord_sat n last xs 2 hxs_len (by omega)).2 hno'
    omega
  | cons c rest ih =>
    let mid := applyWord (clauseWord n c ++ NEXT)
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
          (List.replicate ((c :: rest).length + 2) .Q))) START_POS
    show xs.length * ALIGN.length + formulaState n xs rest last
        (mid - xs.length * ALIGN.length) ≥ _
    have h_inner : formulaState n xs rest last (mid - xs.length * ALIGN.length) ≥
        (rest.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
      rcases Classical.em (∃ vars, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
          ∧ satisfiesClause vars c) with ⟨vars₀, hvars₀, hxs₀, hsat₀⟩ | hnc
      · have h_mid := (clauseNext_sat n c xs ((c :: rest).length + 2) hxs_len (by omega)).1
          vars₀ hvars₀ hxs₀ hsat₀
        rw [show mid = xs.length * ALIGN.length from h_mid,
            show xs.length * ALIGN.length - xs.length * ALIGN.length = START_POS from by
              unfold START_POS; omega]
        exact ih (not_satisfiesFormula_rest n xs c rest hno ⟨vars₀, hvars₀, hxs₀, hsat₀⟩)
      · have := (clauseNext_sat n c xs ((c :: rest).length + 2) hxs_len (by omega)).2 hnc
        exact formulaState_penalty n xs rest last _ hxs_len (by omega)
    have : ((c :: rest).length + 1) * (xs.length * ALIGN.length) =
        xs.length * ALIGN.length + (rest.length + 1) * (xs.length * ALIGN.length) := by
      simp [List.length_cons, Nat.succ_mul]; omega
    omega

/-- If no matching assignment satisfies all of clauses_ ++ [last], then
    formulaState reaches the penalty bound.
    Case splits on whether init (clauses_) is satisfiable:
    - No: formulaState_penalty_start.
    - Yes (some vars₀ satisfies init but not last): formulaState_forward
      gives init.length * block + formulaState([], last, START_POS),
      and clauseWord_sat part 2 bounds the last clause. -/
theorem formulaState_penalty_all (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause)
    (hxs_len : xs.length = n + 1)
    (hno : ¬ (∃ vars : List Bool, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesFormula vars (clauses_ ++ [last]))) :
    formulaState n xs clauses_ last START_POS ≥
      (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
  rcases Classical.em (∃ vars, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
      ∧ satisfiesFormula vars clauses_) with ⟨vars₀, hvars₀, hxs₀, hsat₀⟩ | hno_init
  · -- vars₀ satisfies init but not last
    have hno_last : ¬ (∃ vars, vars.length = n ∧ xs = embedVars vars ++ [PileType.Q]
        ∧ satisfiesClause vars last) := by
      intro ⟨vars', hvars', hxs', hsat'⟩
      have : vars' = vars₀ := embedVars_injective vars' vars₀ (by
        have := hxs₀ ▸ hxs'; simp at this; exact this.symm)
      subst this
      exact hno ⟨vars', hvars', hxs', fun cl hmem => by
        rcases List.mem_append.mp hmem with h | h
        · exact hsat₀ cl h
        · exact (List.mem_singleton.mp h) ▸ hsat'⟩
    rw [formulaState_forward n xs clauses_ last vars₀ hxs_len hvars₀ hxs₀ hsat₀]
    simp only [formulaState, List.length_nil, Nat.zero_add]
    have := (clauseWord_sat n last xs 2 hxs_len (by omega)).2 hno_last
    have : clauses_.length * (xs.length * ALIGN.length) + (xs.length * ALIGN.length + CHAIN_DISQ) =
        (clauses_.length + 1) * (xs.length * ALIGN.length) + CHAIN_DISQ := by
      simp [Nat.succ_mul]; omega
    omega
  · exact formulaState_penalty_start n xs clauses_ last hxs_len hno_init

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
    advances past the first block (via clauseNext_advance), we peel off
    that block and recurse on inner types with the remaining formula word. -/
theorem formulaState_eq (n : Nat) (xs : List PileType)
    (init : List Clause) (last : Clause) (start : Nat)
    (hxs_len : xs.length = n + 1) :
    formulaState n xs init last start =
      applyWord (formulaWord n (init ++ [last]))
        (compile (virtualPileTypes (virtualPileTypes ALIGN xs)
          (List.replicate (init.length + 2) .Q))) start := by
  induction init generalizing start with
  | nil =>
    simp only [formulaState]
    have hfw : formulaWord n ([] ++ [last]) = clauseWord n last := by
      rw [formulaWord_split]; simp
    rw [hfw]
  | cons c rest ih =>
    unfold formulaState; simp only []
    rw [ih]
    symm
    rw [formulaWord_cons, applyWord_append]
    have h_types : virtualPileTypes (virtualPileTypes ALIGN xs)
        (List.replicate ((c :: rest).length + 2) .Q) =
      virtualPileTypes ALIGN xs ++
        virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q) := by
      show virtualPileTypes _ (List.replicate (rest.length + 2 + 1) .Q) = _
      rw [virtualPileTypes_replicate_Q_cons]
    rw [h_types]
    have hmid : xs.length * ALIGN.length ≤
        applyWord (clauseWord n c ++ NEXT)
          (compile (virtualPileTypes ALIGN xs ++
            virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (rest.length + 2) .Q)))
          start := by
      rw [← h_types]
      exact clauseNext_advance n c xs _ start hxs_len (by omega)
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

/-- Forward direction: a satisfying assignment implies acceptance.

    Goal: applyWord(formulaWord)(compile types)(0) < types.length,
    where types has clauses.length Q-reps (= init.length + 1 blocks).

    1. Split clauses = init ++ [last].
    2. types_ext := types with init.length + 2 Q-reps = types ++ one block.
    3. formulaState_eq (uses clauseNext_advance internally):
       formulaState(init, last, 0) = applyWord(formulaWord)(compile types_ext)(0).
    4. formulaState_forward: formulaState = init.length * block + formulaState([], last, 0).
       formulaState([], last, 0) = applyWord(clauseWord last)(types₂)(0).
    5. clauseWord_sat part 1: that = END_POS + n * ALIGN.length = 5 + 6n.
    6. Total = init.length * block + 5 + 6n < init.length * block + 6(n+1)
             = (init.length + 1) * block = clauses.length * block = types.length.
       So result on ext < types.length.
    7. applyWord_append_truncate: result on types = min(result on ext, types.length).
       Since result on ext < types.length, result on types = result on ext < types.length.
       Hence accepts. -/
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
  intro types
  -- 1. Split clauses = init ++ [last]
  obtain ⟨init, last, rfl, hlen⟩ := list_split_last clauses hne
  -- 2. types_ext = types ++ one block
  have h_ext : virtualPileTypes (virtualPileTypes ALIGN xs)
      (List.replicate (init.length + 2) .Q) =
    virtualPileTypes (virtualPileTypes ALIGN xs)
      (List.replicate (init.length + 1) .Q) ++
    virtualPileTypes ALIGN xs := by
    rw [show init.length + 2 = init.length + 1 + 1 from by omega,
        replicate_succ_append, virtualPileTypes_append]
    simp [virtualPileTypes, List.flatMap_cons, List.flatMap_nil, applyPile]
  -- 3. formulaState_eq
  have h_eq := formulaState_eq n xs init last START_POS hxs_len
  -- 4. formulaState_forward
  have h_fwd := formulaState_forward n xs init last vars hxs_len hn hxs
    (fun cl hmem => hsat cl (List.mem_append_left _ hmem))
  -- 5. clauseWord_sat part 1 for last
  have hsat_last : satisfiesClause vars last :=
    hsat last (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have h_cw := (clauseWord_sat n last xs 2 hxs_len (by omega)).1 vars hn hxs hsat_last
  -- 6. Compute total: init.length * block + END_POS + n * ALIGN.length < types.length
  unfold accepts
  -- 7. Truncation: result on types = min(result on ext, types.length)
  have h_trunc := applyWord_append_truncate (formulaWord n (init ++ [last]))
    (virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate (init.length + 1) .Q))
    (virtualPileTypes ALIGN xs) 0 (Nat.zero_le _)
  rw [show (0 : Nat) = START_POS from rfl] at h_trunc
  rw [← h_ext, ← h_eq] at h_trunc
  rw [h_fwd] at h_trunc
  simp only [formulaState, List.length_nil, Nat.zero_add] at h_trunc
  rw [h_cw] at h_trunc
  rw [show (0 : Nat) = START_POS from rfl, h_trunc]
  simp [virtualPileTypes_length, Nat.min_def, hlen]
  unfold END_POS ALIGN; simp
  omega

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
