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

/-- Orient an assignment according to a pile type: `Q` preserves the inner
    order, while `S` reverses it. -/
def orient {n m : Nat} (pt : PileType) (assign : Fin n → Fin m) : Fin n → Fin m :=
  match pt with
  | .Q => assign
  | .S => fun c => Fin.rev (assign c)

/-- The combined pile assignment for two rounds.
    Card c goes to virtual pile (assign2 c) * pt1.length + j, where j is:
    - assign1 c            if pt2[assign2 c] = Q  (Q preserves round-1 order)
    - Fin.rev (assign1 c)  if pt2[assign2 c] = S  (S reverses round-1 order) -/
def combinedAssign {n : Nat} (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    Fin n → Fin (virtualPileTypes pt1 pt2).length :=
  fun c =>
    let j : Fin pt1.length := orient (pt2.get (assign2 c)) assign1 c
    ⟨(assign2 c).val * pt1.length + j.val,
      by rw [virtualPileTypes_length]; exact block_index_bound (assign2 c).isLt j.isLt⟩

/-- Package the two-round binary composition as a single `ShuffleSpec`.
    TODO: move the binary assignment-combination logic directly under this
    spec-level operation, rather than treating `combinedAssign` as the primary
    interface. -/
def combinedSpec {n : Nat} (spec1 spec2 : ShuffleSpec n) : ShuffleSpec n where
  types := virtualPileTypes spec1.types spec2.types
  assign := combinedAssign spec1.types spec2.types spec1.assign spec2.assign

/-- A deck is determined by the strict order it induces on cards. -/
private theorem deck_eq_of_order_iff {n : Nat} (d1 d2 : Deck n)
    (hord : ∀ s t : Fin n, d1.posOf s < d1.posOf t ↔ d2.posOf s < d2.posOf t) :
    d1 = d2 := by
  have hcardAt : d1.cardAt = d2.cardAt := by
    funext k
    have hmono : ∀ j (hj : j + 1 < n),
        d2.posOf (d1.cardAt ⟨j, by omega⟩) <
        d2.posOf (d1.cardAt ⟨j + 1, hj⟩) := by
      intro j hj
      have hk : d1.posOf (d1.cardAt ⟨j, by omega⟩) <
          d1.posOf (d1.cardAt ⟨j + 1, hj⟩) := by
        simpa [d1.right_inv]
      exact (hord _ _).mp hk
    have hid := strictMono_consec_is_id (fun x => d2.posOf (d1.cardAt x)) hmono k
    have hpos : d2.posOf (d1.cardAt k) = k := hid
    have hcard := congrArg d2.cardAt hpos
    simpa [d2.left_inv] using hcard
  apply Deck.ext
  · funext c
    apply d2.cardAt_injective
    have hc1 : d2.cardAt (d1.posOf c) = c := by
      simpa [hcardAt] using d1.left_inv c
    exact hc1.trans (d2.left_inv c).symm
  · exact hcardAt

/-- Binary spec composition should reassociate in the same order as sequential
    shuffle rounds. -/
theorem combinedSpec_assoc {n : Nat}
    (spec1 spec2 spec3 : ShuffleSpec n) :
    combinedSpec (combinedSpec spec1 spec2) spec3 =
    combinedSpec spec1 (combinedSpec spec2 spec3) := by
  sorry -- But it seems like we don't need it...

/-- Two rounds of pile shuffle equal one round on virtual pile types with the
    combined assignment. -/
theorem shuffleRound_virtualPileTypes {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    shuffleRound (shuffleRound d pt1 assign1) pt2 assign2 =
    shuffleRound d (virtualPileTypes pt1 pt2) (combinedAssign pt1 pt2 assign1 assign2) := by
  sorry

/-- Virtual pile type composition should reassociate in the same order as
    sequential shuffle rounds.  This is recorded here as a potential algebraic
    helper for future-oriented fold proofs. -/
theorem virtualPileTypes_assoc (pt1 pt2 pt3 : List PileType) :
    virtualPileTypes (virtualPileTypes pt1 pt2) pt3 =
    virtualPileTypes pt1 (virtualPileTypes pt2 pt3) := by
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

/-- Package the binary inverse of `combinedAssign` at the `ShuffleSpec` level.
    Given explicit component type lists and a combined spec whose types match
    their virtual composition, recover the two component specs by splitting the
    combined assignment cardwise. -/
def splitSpec {n : Nat} (spec : ShuffleSpec n) (pt1 pt2 : List PileType)
    (h : spec.types = virtualPileTypes pt1 pt2) :
    ShuffleSpec n × ShuffleSpec n :=
  let split := fun c => splitAssign pt1 pt2 ((spec.assign c).cast (by simpa [h]))
  ( { types := pt1
      assign := fun c => (split c).1 }
  , { types := pt2
      assign := fun c => (split c).2 } )

/-- Splitting a combined spec and recombining the two recovered component specs
    gives back the original combined spec. -/
theorem combinedSpec_splitSpec {n : Nat}
    (spec : ShuffleSpec n) (pt1 pt2 : List PileType)
    (h : spec.types = virtualPileTypes pt1 pt2) :
    combinedSpec (splitSpec spec pt1 pt2 h).1 (splitSpec spec pt1 pt2 h).2 = spec := by
  sorry

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
    simp only [combinedAssign, splitAssign, orient, h', fin_rev_rev]
    exact div_mul_add_mod v.val pt1.length

-- `combinedAssign` respects pointwise equality of input assignments.
private theorem combinedAssign_congr {n : Nat} (pt1 pt2 : List PileType)
    (assign1 assign1' : Fin n → Fin pt1.length)
    (assign2 assign2' : Fin n → Fin pt2.length) (c : Fin n)
    (h1 : assign1 c = assign1' c) (h2 : assign2 c = assign2' c) :
    combinedAssign pt1 pt2 assign1 assign2 c =
    combinedAssign pt1 pt2 assign1' assign2' c := by
  apply Fin.ext
  have h1v : (assign1 c).val = (assign1' c).val := congrArg Fin.val h1
  have h2v : (assign2 c).val = (assign2' c).val := congrArg Fin.val h2
  cases h : pt2.get (assign2 c)
  · have h' : pt2.get (assign2' c) = .Q := by simpa [h2] using h
    simp only [combinedAssign, orient, h, h', h2v]
    exact congrArg (fun x => (assign2' c).val * pt1.length + x) h1v
  · have h' : pt2.get (assign2' c) = .S := by simpa [h2] using h
    simp only [combinedAssign, orient, h, h', h2v, Fin.val_rev]
    exact congrArg (fun x => (assign2' c).val * pt1.length + (pt1.length - (x + 1))) h1v

/-- Output val depends only on the two input assignment values for the given
    card. -/
theorem combinedAssign_val_congr {n : Nat} (pt1 pt2 : List PileType)
    (assign1 assign1' : Fin n → Fin pt1.length)
    (assign2 assign2' : Fin n → Fin pt2.length) (c : Fin n)
    (h1 : (assign1 c).val = (assign1' c).val)
    (h2 : (assign2 c).val = (assign2' c).val) :
    (combinedAssign pt1 pt2 assign1 assign2 c).val =
    (combinedAssign pt1 pt2 assign1' assign2' c).val :=
  congrArg Fin.val (combinedAssign_congr pt1 pt2 assign1 assign1' assign2 assign2' c
    (Fin.ext h1) (Fin.ext h2))

/-- Val-level roundtrip: if the two component assignments match the pieces
    returned by `splitAssign`, then `combinedAssign` recovers the original
    virtual-pile value. -/
theorem combinedAssign_split_val (pt1 pt2 : List PileType)
    (v : Fin (virtualPileTypes pt1 pt2).length) {n : Nat}
    (assign1 : Fin n → Fin pt1.length) (assign2 : Fin n → Fin pt2.length) (c : Fin n)
    (h1 : (assign1 c).val = (splitAssign pt1 pt2 v).1.val)
    (h2 : (assign2 c).val = (splitAssign pt1 pt2 v).2.val) :
    (combinedAssign pt1 pt2 assign1 assign2 c).val = v.val :=
  (combinedAssign_val_congr pt1 pt2 assign1 _ assign2 _ c h1 h2).trans
    (congrArg Fin.val (combinedAssign_split pt1 pt2 v c))
