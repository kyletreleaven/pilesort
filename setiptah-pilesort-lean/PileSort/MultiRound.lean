/-
  Multi-round pile shuffle.

  A `ShuffleSpec n` bundles a pile-type list with a deal assignment for one
  round.  `multiShuffleRound` applies a sequence of specs to a deck via
  `shuffleRound`, folding left.

  ## Status

  `formulaWord_correct_sortable` ✅ — single-round form.
  `splitAssign` ✅, `foldedAssign` ✅, `multiShuffleRound_eq_shuffleRound` ✅ (def),
  `formulaWord_correct_multiSortable` ✅ — proved modulo sorries below.

  ## Remaining sorries

  ### `shuffleRound_virtualPileTypes`
  Two rounds on pt1, pt2 equal one round on `virtualPileTypes pt1 pt2`
  with `combinedAssign`.  This is the main hard lemma; everything else
  follows from it.

  ### `multiShuffleRound_eq_shuffleRound`
  Fold version: `multiShuffleRound d specs = shuffleRound d
  (foldVirtualPileTypes (specs.map (·.types))) (foldedAssign specs)`.
  Proved by induction using `shuffleRound_virtualPileTypes`.

  ### `combinedAssign_split`
  Roundtrip: `combinedAssign pt1 pt2 (splitAssign v).1 (splitAssign v).2 = v`.
  Arithmetic on the block encoding `v = b * pt1.length + j`.

  ### `unfoldedAssign` + `multiSortable_iff_sortable`
  `unfoldedAssign` splits a single combined assign back into per-round assigns
  by iterating `splitAssign`; it is the inverse of `foldedAssign`.
  `multiSortable_iff_sortable` then follows constructively:
  · forward  — `foldedAssign specs` witnesses `Sortable`;
  · backward — `unfoldedAssign assign` reconstructs specs, closed by
    `combinedAssign_split`.
-/
import PileSort.PileShuffle
import PileSort.VirtualPileTypes
import PileSort.SortableIff
import PileSort.FormulaWord

/-- One round's worth of pile-shuffle parameters. -/
structure ShuffleSpec (n : Nat) where
  types  : List PileType
  assign : Fin n → Fin types.length

/-- Apply a sequence of shuffle rounds to a deck, left to right. -/
def multiShuffleRound {n : Nat} (d : Deck n) (rounds : List (ShuffleSpec n)) : Deck n :=
  rounds.foldl (fun acc r => shuffleRound acc r.types r.assign) d

/-- A deck is multi-round sortable by a sequence of pile-type lists if there exist
    per-round assignments (of the given types) that together sort the deck. -/
def MultiSortable {n : Nat} (d : Deck n) (rounds : List (List PileType)) : Prop :=
  ∃ specs : List (ShuffleSpec n),
    specs.map (·.types) = rounds ∧
    multiShuffleRound d specs = Deck.sorted n

/-! ## Construction: deck realizing a given word as its change profile -/

/-- Place card `start` first (.a) or last (.d), recurse with start+1.
    `deckSeqNat 0 word` is a permutation of {0,..,word.length} with
    indexOf k < indexOf (k+1) iff word[k] = .a. -/
private def deckSeqNat (start : Nat) : List Action → List Nat
  | []         => [start]
  | .a :: rest => start :: deckSeqNat (start + 1) rest
  | .d :: rest => deckSeqNat (start + 1) rest ++ [start]

private theorem deckSeqNat_length (start : Nat) (word : List Action) :
    (deckSeqNat start word).length = word.length + 1 := by
  induction word generalizing start with
  | nil => simp [deckSeqNat]
  | cons act rest ih => cases act <;> simp [deckSeqNat, ih]

private theorem deckSeqNat_mem (start : Nat) (word : List Action) (k : Nat) :
    k ∈ deckSeqNat start word ↔ start ≤ k ∧ k ≤ start + word.length := by
  induction word generalizing start with
  | nil =>
    simp only [deckSeqNat, List.mem_singleton, List.length_nil, Nat.add_zero]
    constructor <;> intro h <;> omega
  | cons act rest ih =>
    cases act with
    | a =>
      simp only [deckSeqNat, List.mem_cons, ih, List.length_cons]
      constructor
      · rintro (rfl | ⟨h1, h2⟩) <;> omega
      · intro ⟨h1, h2⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact Or.inl rfl
        · exact Or.inr ⟨hlt, by omega⟩
    | d =>
      simp only [deckSeqNat, List.mem_append, List.mem_singleton, ih, List.length_cons]
      constructor
      · rintro (⟨h1, h2⟩ | rfl) <;> omega
      · intro ⟨h1, h2⟩
        rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
        · exact Or.inr rfl
        · exact Or.inl ⟨hlt, by omega⟩

private theorem deckSeqNat_nodup (start : Nat) (word : List Action) :
    (deckSeqNat start word).Nodup := by
  induction word generalizing start with
  | nil => simp [deckSeqNat]
  | cons act rest ih =>
    cases act with
    | a =>
      exact List.nodup_cons.mpr
        ⟨fun h => absurd ((deckSeqNat_mem _ _ _).mp h).1 (by omega), ih _⟩
    | d =>
      simp only [deckSeqNat]
      have hnotmem : start ∉ deckSeqNat (start + 1) rest :=
        fun h => absurd ((deckSeqNat_mem _ _ _).mp h).1 (by omega)
      suffices ∀ (l : List Nat), l.Nodup → start ∉ l → (l ++ [start]).Nodup from
        this _ (ih _) hnotmem
      intro l hnd hni
      induction l with
      | nil => simp
      | cons hd tl ihtl =>
        apply List.nodup_cons.mpr
        constructor
        · intro hmem
          rcases List.mem_append.mp hmem with h | h
          · exact (List.nodup_cons.mp hnd).1 h
          · exact hni (List.mem_singleton.mp h ▸ List.mem_cons_self hd tl)
        · exact ihtl (List.nodup_cons.mp hnd).2
                     (fun h => hni (List.mem_cons_of_mem _ h))

/-- Cast to Fin; bound follows from deckSeqNat_mem. -/
private def deckSeqFin (word : List Action) : List (Fin (word.length + 1)) :=
  (deckSeqNat 0 word).pmap
    (fun k hk => ⟨k, by have := (deckSeqNat_mem 0 word k).mp hk; omega⟩)
    (fun k hk => hk)

private theorem deckSeqFin_length (word : List Action) :
    (deckSeqFin word).length = word.length + 1 := by
  unfold deckSeqFin; rw [List.length_pmap, deckSeqNat_length]

private theorem deckSeqFin_nodup (word : List Action) : (deckSeqFin word).Nodup :=
  (deckSeqNat_nodup 0 word).pmap
    (fun _ hk => hk)
    (fun ⦃_⦄ _ ⦃_⦄ _ hne heq => hne (congrArg Fin.val heq))

/-- A deck whose change profile equals word. -/
def deckOfWord (word : List Action) : Deck (word.length + 1) :=
  Deck.fromDeckSeq (deckSeqFin word) (deckSeqFin_nodup word) (deckSeqFin_length word)

/-! ## indexOf bridge: deckSeqFin ↔ deckSeqNat -/

-- getElem of a pmap into Fin has the same val as the original list,
-- provided the mapping function is val-preserving.
private theorem pmap_getElem_val {m : Nat} {p : Nat → Prop} (f : ∀ k, p k → Fin m)
    (hf : ∀ k h, (f k h).val = k)
    (l : List Nat) (H : ∀ k ∈ l, p k)
    (i : Nat) (hi : i < (l.pmap f H).length) (hi' : i < l.length) :
    ((l.pmap f H)[i]'hi).val = l[i]'hi' := by
  induction l generalizing i with
  | nil => exact absurd hi' (Nat.not_lt_zero _)
  | cons x xs ih =>
    cases i with
    | zero => simp [List.pmap, hf]
    | succ i =>
      simp only [List.pmap, List.getElem_cons_succ]
      exact ih (fun j hj => H j (List.mem_cons_of_mem x hj)) i
               (by simpa [List.length_pmap] using hi) (Nat.lt_of_succ_lt_succ hi')

-- The i-th element of deckSeqFin has the same val as the i-th element of deckSeqNat.
private theorem deckSeqFin_get_val (word : List Action) (i : Nat)
    (hi_fin : i < (deckSeqFin word).length) (hi_nat : i < (deckSeqNat 0 word).length) :
    ((deckSeqFin word)[i]'hi_fin).val = (deckSeqNat 0 word)[i]'hi_nat := by
  unfold deckSeqFin
  exact pmap_getElem_val _ (fun _ _ => rfl) _ _ _ _ hi_nat

private theorem indexOf_pmap_fin (word : List Action) (k : Nat) (hk : k < word.length + 1) :
    (deckSeqFin word).indexOf ⟨k, hk⟩ = (deckSeqNat 0 word).indexOf k := by
  have hmem : k ∈ deckSeqNat 0 word :=
    (deckSeqNat_mem 0 word k).mpr ⟨Nat.zero_le _, by omega⟩
  have hi_lt : (deckSeqNat 0 word).indexOf k < (deckSeqNat 0 word).length :=
    indexOf_lt_length hmem
  have hi_fin : (deckSeqNat 0 word).indexOf k < (deckSeqFin word).length := by
    rwa [deckSeqFin_length, ← deckSeqNat_length]
  have hget : (deckSeqFin word)[(deckSeqNat 0 word).indexOf k]'hi_fin = ⟨k, hk⟩ := by
    apply Fin.ext
    rw [deckSeqFin_get_val _ _ hi_fin hi_lt, getElem_indexOf hmem]
  rw [← hget]
  exact indexOf_getElem (deckSeqFin_nodup word) _ hi_fin

/-! ## Key order lemma -/

/-- indexOf (start+k) in deckSeqNat start word precedes indexOf (start+k+1) iff word[k] = .a. -/
private theorem deckSeqNat_a_zero (start : Nat) (rest : List Action) :
    (start :: deckSeqNat (start + 1) rest).indexOf start <
    (start :: deckSeqNat (start + 1) rest).indexOf (start + 1) := by
  rw [indexOf_cons_eq _ _ _ rfl, indexOf_cons_ne _ _ _ (by omega)]
  omega

private theorem deckSeqNat_d_zero (start : Nat) (rest : List Action) :
    ¬ ((deckSeqNat (start + 1) rest ++ [start]).indexOf start <
       (deckSeqNat (start + 1) rest ++ [start]).indexOf (start + 1)) := by
  have hmem : start + 1 ∈ deckSeqNat (start + 1) rest :=
    (deckSeqNat_mem _ _ _).mpr ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
  have hnotmem : start ∉ deckSeqNat (start + 1) rest :=
    fun h => absurd ((deckSeqNat_mem _ _ _).mp h).1 (by omega)
  rw [indexOf_append_of_mem hmem, indexOf_append_not_mem _ _ hnotmem,
      indexOf_cons_eq start start [] rfl]
  have := indexOf_lt_length hmem
  omega

private theorem indexOf_order_iff_aux (start : Nat) (word : List Action)
    (k : Nat) (hk : k < word.length) :
    (deckSeqNat start word).indexOf (start + k) <
    (deckSeqNat start word).indexOf (start + k + 1) ↔
    word[k]'hk = .a := by
  induction word generalizing start k with
  | nil => exact absurd hk (Nat.not_lt_zero _)
  | cons act rest ih =>
    cases k with
    | zero =>
      simp only [Nat.add_zero]
      cases act with
      | a => simp only [deckSeqNat]
             exact iff_of_true (deckSeqNat_a_zero start rest) rfl
      | d => simp only [deckSeqNat, List.getElem_cons_zero]
             exact iff_of_false (deckSeqNat_d_zero start rest) (by decide)
    | succ k' =>
      have hk' : k' < rest.length := Nat.lt_of_succ_lt_succ hk
      -- normalize Nat.succ k' → k' + 1 so arithmetic rewrites find their targets
      simp only [Nat.succ_eq_add_one] at *
      have eq1 : start + (k' + 1) = (start + 1) + k' := by omega
      cases act with
      | a =>
        simp only [deckSeqNat]
        rw [indexOf_cons_ne _ _ _ (by omega : start ≠ start + (k' + 1)),
            indexOf_cons_ne _ _ _ (by omega : start ≠ start + (k' + 1) + 1),
            eq1, Nat.add_lt_add_iff_right]
        exact ih (start + 1) k' hk'
      | d =>
        simp only [deckSeqNat]
        rw [indexOf_append_of_mem ((deckSeqNat_mem _ _ _).mpr ⟨by omega, by omega⟩),
            indexOf_append_of_mem ((deckSeqNat_mem _ _ _).mpr ⟨by omega, by omega⟩),
            eq1]
        exact ih (start + 1) k' hk'

private theorem indexOf_order_iff (word : List Action) (k : Nat) (hk : k < word.length) :
    (deckSeqNat 0 word).indexOf k < (deckSeqNat 0 word).indexOf (k + 1) ↔
    word[k]'hk = .a := by
  have := indexOf_order_iff_aux 0 word k hk
  simpa using this

/-! ## deckOfWord has the right change profile -/

theorem deckOfWord_changeProfile (word : List Action) :
    Deck.changeProfile (deckOfWord word) = word := by
  apply List.ext_getElem
  · simp [changeProfile_length]
  · intro i hi _
    have hkw : i < word.length := by rw [changeProfile_length] at hi; exact hi
    rw [changeProfile_get (deckOfWord word) i hi]
    -- Match the exact bounds changeProfile_get used in its let-bindings
    have hlt_iff :
        (deckOfWord word).posOf ⟨i, by rw [changeProfile_length] at hi; omega⟩ <
        (deckOfWord word).posOf ⟨i+1, by rw [changeProfile_length] at hi; omega⟩ ↔
        word[i]'hkw = .a := by
      simp only [deckOfWord, Deck.fromDeckSeq, Fin.lt_def]
      rw [indexOf_pmap_fin, indexOf_pmap_fin, indexOf_order_iff _ _ hkw]
    simp only [hlt_iff]
    cases word[i]'hkw <;> rfl

/-! ## Two-round reduction to single round on virtual pile types -/

/-- The combined pile assignment for two rounds.
    Card c goes to virtual pile (assign2 c) * pt1.length + j, where j is:
    - assign1 c            if pt2[assign2 c] = Q  (Q preserves round-1 order)
    - Fin.rev (assign1 c)  if pt2[assign2 c] = S  (S reverses round-1 order) -/
def combinedAssign {n : Nat} (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    Fin n → Fin (virtualPileTypes pt1 pt2).length :=
  fun c =>
    let j : Fin pt1.length := match pt2.get (assign2 c) with
      | .Q => assign1 c
      | .S => Fin.rev (assign1 c)
    ⟨(assign2 c).val * pt1.length + j.val,
      by rw [virtualPileTypes_length]; exact block_index_bound (assign2 c).isLt j.isLt⟩

/-- Two rounds of pile shuffle equal one round on virtual pile types with the
    combined assignment. -/
theorem shuffleRound_virtualPileTypes {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    shuffleRound (shuffleRound d pt1 assign1) pt2 assign2 =
    shuffleRound d (virtualPileTypes pt1 pt2) (combinedAssign pt1 pt2 assign1 assign2) := by
  sorry

/-- Main reduction theorem: the deck realizing a formula word is sortable by the
    pile-sort machine iff the formula is satisfiable. -/
theorem formulaWord_correct_sortable (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    let types := virtualPileTypes (virtualPileTypes ALIGN xs) (List.replicate clauses.length PileType.Q)
    Sortable (deckOfWord (formulaWord n clauses)) types ↔
      HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  intro types
  rw [sortable_iff_accepts (Nat.succ_pos _), deckOfWord_changeProfile]
  exact formulaWord_correct n clauses xs hn hxs_len hne

/-! ## Inverse of `combinedAssign` -/

/-- Decode a virtual-pile index back into its component pile indices.
    The block encoding `v = b * pt1.length + j` (with `j` reversed when
    `pt2[b] = S`) uniquely determines both component assignments. -/
def splitAssign (pt1 pt2 : List PileType)
    (v : Fin (virtualPileTypes pt1 pt2).length) :
    Fin pt1.length × Fin pt2.length :=
  have hv : v.val < pt2.length * pt1.length :=
    virtualPileTypes_length pt1 pt2 ▸ v.isLt
  have hpt1 : 0 < pt1.length := by
    rcases Nat.eq_zero_or_pos pt1.length with h | h
    · simp [h] at hv
    · exact h
  let b : Fin pt2.length :=
    ⟨v.val / pt1.length, (Nat.div_lt_iff_lt_mul hpt1).mpr hv⟩
  let j : Fin pt1.length := ⟨v.val % pt1.length, Nat.mod_lt _ hpt1⟩
  match pt2.get b with
  | .Q => (j, b)
  | .S => (Fin.rev j, b)

/-! ## Folding assignments over a spec list -/

private def foldedAssignAux {n : Nat}
    (acc : List PileType) (f : Fin n → Fin acc.length) :
    (specs : List (ShuffleSpec n)) →
    Fin n → Fin (specs.foldl (fun t s => virtualPileTypes t s.types) acc).length
  | []        => f
  | s :: rest =>
    foldedAssignAux
      (virtualPileTypes acc s.types)
      (combinedAssign acc s.types f s.assign)
      rest

/-- Fold a list of per-round assignments into a single combined assignment
    into `foldVirtualPileTypes rounds`. -/
def foldedAssign {n : Nat} (specs : List (ShuffleSpec n)) :
    Fin n → Fin (foldVirtualPileTypes (specs.map (·.types))).length :=
  fun c => Fin.cast
    (congrArg List.length (by simp [foldVirtualPileTypes, List.foldl_map]))
    (foldedAssignAux [PileType.Q] (fun _ => ⟨0, by simp⟩) specs c)

/-! ## Fold version of `shuffleRound_virtualPileTypes` -/

/-- Applying a sequence of shuffle rounds equals one shuffle round on the
    folded virtual pile types with the folded assignment. -/
theorem multiShuffleRound_eq_shuffleRound {n : Nat} (d : Deck n)
    (specs : List (ShuffleSpec n)) :
    multiShuffleRound d specs =
    shuffleRound d
      (foldVirtualPileTypes (specs.map (·.types)))
      (foldedAssign specs) := by
  sorry

/-- Multi-round sortability is equivalent to single-round sortability on the
    folded virtual pile types. -/
theorem multiSortable_iff_sortable {n : Nat} (d : Deck n)
    (rounds : List (List PileType)) :
    MultiSortable d rounds ↔ Sortable d (foldVirtualPileTypes rounds) := by
  sorry

/-- Main reduction theorem (multi-round form): the deck realizing a formula word is
    sortable in three rounds (ALIGN, xs, replicate Q) iff the formula is satisfiable. -/
theorem formulaWord_correct_multiSortable (n : Nat) (clauses : List Clause)
    (xs : List PileType)
    (hn : n ≥ 1)
    (hxs_len : xs.length = n + 1)
    (hne : clauses ≠ []) :
    MultiSortable (deckOfWord (formulaWord n clauses))
      [ALIGN, xs, List.replicate clauses.length PileType.Q] ↔
      HasMatchingAssignment n xs (satisfiesFormula · clauses) := by
  rw [multiSortable_iff_sortable]
  simp only [foldVirtualPileTypes, List.foldl, virtualPileTypes_leftId]
  exact formulaWord_correct_sortable n clauses xs hn hxs_len hne
