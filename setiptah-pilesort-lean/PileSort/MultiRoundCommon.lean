import PileSort.ChangeProfiles
import PileSort.VirtualPileTypes

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
