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
import PileSort.ChangeProfiles
import PileSort.VirtualPileTypes
import PileSort.SortableIff
import PileSort.FormulaWord
import PileSort.ChangeProfiles

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

-- n / k * k + n % k = n  (Nat.div_add_mod uses the other multiplication order)
private theorem div_mul_add_mod (n k : Nat) : n / k * k + n % k = n := by
  rw [Nat.mul_comm]; exact Nat.div_add_mod n k

-- Fin.rev is an involution.
private theorem fin_rev_rev {n : Nat} (i : Fin n) : Fin.rev (Fin.rev i) = i :=
  Fin.ext (by simp [Fin.val_rev])

/-- `splitAssign` is a left inverse of `combinedAssign`: decoding the virtual-pile
    index produced by combining two component assigns recovers the original index. -/
theorem combinedAssign_split (pt1 pt2 : List PileType)
    (v : Fin (virtualPileTypes pt1 pt2).length) {n : Nat} (c : Fin n) :
    combinedAssign pt1 pt2
      (fun _ => (splitAssign pt1 pt2 v).1)
      (fun _ => (splitAssign pt1 pt2 v).2) c = v := by
  apply Fin.ext
  have hv : v.val < pt2.length * pt1.length := virtualPileTypes_length pt1 pt2 ▸ v.isLt
  have hpt1 : 0 < pt1.length := by
    rcases Nat.eq_zero_or_pos pt1.length with h | h; simp [h] at hv; exact h
  have hb : v.val / pt1.length < pt2.length := (Nat.div_lt_iff_lt_mul hpt1).mpr hv
  -- h' lets simp evaluate pt2.get at the block index regardless of proof term.
  cases h : pt2.get ⟨v.val / pt1.length, hb⟩ with
  | Q =>
    have h' : ∀ p, pt2.get ⟨v.val / pt1.length, p⟩ = .Q :=
      fun p => (congrArg pt2.get (Fin.ext rfl)).trans h
    simp only [combinedAssign, splitAssign, h']
    exact div_mul_add_mod v.val pt1.length
  | S =>
    have h' : ∀ p, pt2.get ⟨v.val / pt1.length, p⟩ = .S :=
      fun p => (congrArg pt2.get (Fin.ext rfl)).trans h
    simp only [combinedAssign, splitAssign, h', fin_rev_rev]
    exact div_mul_add_mod v.val pt1.length

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

/-! ## Backward direction helpers for `multiSortable_iff_sortable` -/

-- Structural recursion on the reversed round list: each cons peels one round
-- from the right of the original, splitting the assign via `splitAssign`.
private def unfoldedAssignAux {n : Nat} :
    (rev : List (List PileType)) →
    (Fin n → Fin (foldVirtualPileTypes rev.reverse).length) →
    List (ShuffleSpec n)
  | [], _ => []
  | last :: rest, assign =>
    have hfold : foldVirtualPileTypes (last :: rest).reverse =
        virtualPileTypes (foldVirtualPileTypes rest.reverse) last := by
      simp [List.reverse_cons, foldVirtualPileTypes_append_singleton]
    let split := fun c => splitAssign (foldVirtualPileTypes rest.reverse) last
                   ((assign c).cast (congrArg List.length hfold))
    unfoldedAssignAux rest (fun c => (split c).1) ++ [⟨last, fun c => (split c).2⟩]

private def unfoldedAssign {n : Nat} (rounds : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypes rounds).length) :
    List (ShuffleSpec n) :=
  unfoldedAssignAux rounds.reverse
    (fun c => (assign c).cast (by simp [foldVirtualPileTypes, List.reverse_reverse]))

private theorem unfoldedAssignAux_types {n : Nat} :
    ∀ (rev : List (List PileType))
      (assign : Fin n → Fin (foldVirtualPileTypes rev.reverse).length),
    (unfoldedAssignAux rev assign).map (·.types) = rev.reverse
  | [],            _      => rfl
  | last :: rest,  assign => by
    simp only [unfoldedAssignAux, List.map_append, List.map_singleton]
    rw [unfoldedAssignAux_types rest]
    simp [List.reverse_cons]

private theorem unfoldedAssign_types {n : Nat} (rounds : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypes rounds).length) :
    (unfoldedAssign rounds assign).map (·.types) = rounds := by
  simp [unfoldedAssign, unfoldedAssignAux_types]

private theorem shuffleRound_congr_val {n : Nat} (d : Deck n)
    (types1 types2 : List PileType) (h : types1 = types2)
    (assign1 : Fin n → Fin types1.length) (assign2 : Fin n → Fin types2.length)
    (hval : ∀ c, (assign1 c).val = (assign2 c).val) :
    shuffleRound d types1 assign1 = shuffleRound d types2 assign2 := by
  subst h
  exact congrArg (shuffleRound d types1) (funext (fun c => Fin.ext (hval c)))

-- `foldedAssign` on a snoc list equals `combinedAssign` of the folded prefix
-- with the last spec.  Follows from left-fold structure of `foldedAssignAux`.
private theorem foldedAssign_snoc_val {n : Nat}
    (specs : List (ShuffleSpec n)) (types : List PileType)
    (sassign : Fin n → Fin types.length) (c : Fin n) :
    (foldedAssign (specs ++ [⟨types, sassign⟩]) c).val =
    (combinedAssign (foldVirtualPileTypes (specs.map (·.types))) types
                    (foldedAssign specs) sassign c).val := sorry

-- `combinedAssign` respects pointwise equality of input assignments.
private theorem combinedAssign_congr {n : Nat} (pt1 pt2 : List PileType)
    (assign1 assign1' : Fin n → Fin pt1.length)
    (assign2 assign2' : Fin n → Fin pt2.length) (c : Fin n)
    (h1 : assign1 c = assign1' c) (h2 : assign2 c = assign2' c) :
    combinedAssign pt1 pt2 assign1 assign2 c =
    combinedAssign pt1 pt2 assign1' assign2' c := by
  simp only [combinedAssign, h1, h2]

-- Output val depends only on input vals.
private theorem combinedAssign_val_congr {n : Nat} (pt1 pt2 : List PileType)
    (assign1 assign1' : Fin n → Fin pt1.length)
    (assign2 assign2' : Fin n → Fin pt2.length) (c : Fin n)
    (h1 : (assign1 c).val = (assign1' c).val)
    (h2 : (assign2 c).val = (assign2' c).val) :
    (combinedAssign pt1 pt2 assign1 assign2 c).val =
    (combinedAssign pt1 pt2 assign1' assign2' c).val :=
  congrArg Fin.val (combinedAssign_congr pt1 pt2 assign1 assign1' assign2 assign2' c
    (Fin.ext h1) (Fin.ext h2))

-- Val-level roundtrip: follows from congruence + `combinedAssign_split`.
private theorem combinedAssign_split_val (pt1 pt2 : List PileType)
    (v : Fin (virtualPileTypes pt1 pt2).length) {n : Nat}
    (assign1 : Fin n → Fin pt1.length) (assign2 : Fin n → Fin pt2.length) (c : Fin n)
    (h1 : (assign1 c).val = (splitAssign pt1 pt2 v).1.val)
    (h2 : (assign2 c).val = (splitAssign pt1 pt2 v).2.val) :
    (combinedAssign pt1 pt2 assign1 assign2 c).val = v.val :=
  (combinedAssign_val_congr pt1 pt2 assign1 _ assign2 _ c h1 h2).trans
    (congrArg Fin.val (combinedAssign_split pt1 pt2 v c))

-- Changing the first folded pile-type list along an equality preserves the
-- combined assignment value, provided the first component assignment value is
-- preserved pointwise.
private theorem combinedAssign_val_congr_first {n : Nat}
    (pt1 pt1' pt2 : List PileType)
    (h : pt1 = pt1')
    (assign1 : Fin n → Fin pt1.length)
    (assign1' : Fin n → Fin pt1'.length)
    (assign2 : Fin n → Fin pt2.length)
    (c : Fin n)
    (hval : (assign1 c).val = (assign1' c).val) :
    (combinedAssign pt1 pt2 assign1 assign2 c).val =
    (combinedAssign pt1' pt2 assign1' assign2 c).val := by
  subst h
  cases hget : pt2[(assign2 c).val] with
  | Q =>
      simpa [combinedAssign, hget] using hval
  | S =>
      have hrev : (Fin.rev (assign1 c)).val = (Fin.rev (assign1' c)).val := by
        simp [Fin.val_rev, hval]
      simpa [combinedAssign, hget] using hrev


-- Standard snoc induction for lists (not in Lean 4 core).
private def reverseRecAux {α : Type} {C : List α → Sort _}
    (H0 : C []) (H1 : ∀ init last, C init → C (init ++ [last])) :
    (rev : List α) → C rev.reverse
  | [] => by simpa using H0
  | last :: rest => by
      have ih : C rest.reverse := reverseRecAux H0 H1 rest
      simpa [List.reverse_cons] using H1 rest.reverse last ih

private def reverseRecOn {α : Type} {C : List α → Sort _} (l : List α)
    (H0 : C []) (H1 : ∀ init last, C init → C (init ++ [last])) : C l := by
  simpa using reverseRecAux H0 H1 l.reverse

-- Unfolding `init ++ [last]` gives the unfolding of `init` followed by one spec for `last`.
private theorem unfoldedAssign_snoc {n : Nat} (init : List (List PileType))
    (last : List PileType)
    (assign : Fin n → Fin (foldVirtualPileTypes (init ++ [last])).length) :
    let hfold := foldVirtualPileTypes_append_singleton init last
    let v := fun c => (assign c).cast (congrArg List.length hfold)
    unfoldedAssign (init ++ [last]) assign =
    unfoldedAssign init (fun c => (splitAssign (foldVirtualPileTypes init) last (v c)).1) ++
    [⟨last, fun c => (splitAssign (foldVirtualPileTypes init) last (v c)).2⟩] := by
  sorry

-- The val-roundtrip: foldedAssign undoes unfoldedAssign pointwise.
private theorem foldedAssign_unfoldedAssign_val {n : Nat} (rounds : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypes rounds).length) (c : Fin n) :
    (foldedAssign (unfoldedAssign rounds assign) c).val = (assign c).val := by
  revert assign
  apply reverseRecOn rounds
  · intro assign
    simp [unfoldedAssign, unfoldedAssignAux, foldedAssign, foldedAssignAux, foldVirtualPileTypes]
  · intro init last ih assign
    rw [unfoldedAssign_snoc init last assign, foldedAssign_snoc_val]
    let v : Fin n → Fin (foldVirtualPileTypes (init ++ [last])).length := fun c => assign c
    let prefixAssign : Fin n → Fin (foldVirtualPileTypes init).length :=
      fun c =>
        (splitAssign (foldVirtualPileTypes init) last
          ((v c).cast (congrArg List.length
            (foldVirtualPileTypes_append_singleton init last)))).1
    let suffixAssign : Fin n → Fin last.length :=
      fun c =>
        (splitAssign (foldVirtualPileTypes init) last
          ((v c).cast (congrArg List.length
            (foldVirtualPileTypes_append_singleton init last)))).2
    have htypes : (unfoldedAssign init prefixAssign).map (·.types) = init :=
      unfoldedAssign_types init prefixAssign
    have hprefix :
        (foldedAssign (unfoldedAssign init prefixAssign) c).val = (prefixAssign c).val := by
      simpa [prefixAssign] using ih prefixAssign
    have hstep :
        (combinedAssign
          (foldVirtualPileTypes ((unfoldedAssign init prefixAssign).map (·.types)))
          last
          (foldedAssign (unfoldedAssign init prefixAssign))
          suffixAssign c).val =
        (combinedAssign (foldVirtualPileTypes init) last
          prefixAssign suffixAssign c).val := by
      exact combinedAssign_val_congr_first
        (foldVirtualPileTypes ((unfoldedAssign init prefixAssign).map (·.types)))
        (foldVirtualPileTypes init)
        last
        (congrArg foldVirtualPileTypes htypes)
        (foldedAssign (unfoldedAssign init prefixAssign))
        prefixAssign
        suffixAssign
        c
        hprefix
    exact hstep.trans <|
      combinedAssign_split_val (foldVirtualPileTypes init) last
        ((v c).cast (congrArg List.length
          (foldVirtualPileTypes_append_singleton init last)))
        prefixAssign suffixAssign c rfl rfl

-- Bundles `unfoldedAssign_types` + `foldedAssign_unfoldedAssign_val` into the
-- shuffle equality needed by `multiSortable_iff_sortable`.
private theorem foldedAssign_unfoldedAssign_shuffle {n : Nat} (d : Deck n)
    (rounds : List (List PileType))
    (assign : Fin n → Fin (foldVirtualPileTypes rounds).length) :
    shuffleRound d (foldVirtualPileTypes ((unfoldedAssign rounds assign).map (·.types)))
                   (foldedAssign (unfoldedAssign rounds assign)) =
    shuffleRound d (foldVirtualPileTypes rounds) assign :=
  shuffleRound_congr_val d _ _
    (congrArg foldVirtualPileTypes (unfoldedAssign_types rounds assign))
    _ _ (foldedAssign_unfoldedAssign_val rounds assign)

/-- Multi-round sortability is equivalent to single-round sortability on the
    folded virtual pile types. -/
theorem multiSortable_iff_sortable {n : Nat} (d : Deck n)
    (rounds : List (List PileType)) :
    MultiSortable d rounds ↔ Sortable d (foldVirtualPileTypes rounds) := by
  constructor
  · rintro ⟨specs, htypes, hresult⟩
    subst htypes
    exact ⟨foldedAssign specs,
           (multiShuffleRound_eq_shuffleRound d specs).symm.trans hresult⟩
  · rintro ⟨assign, hresult⟩
    exact ⟨unfoldedAssign rounds assign, unfoldedAssign_types rounds assign,
           (multiShuffleRound_eq_shuffleRound d (unfoldedAssign rounds assign)).trans
           ((foldedAssign_unfoldedAssign_shuffle d rounds assign).trans hresult)⟩

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
