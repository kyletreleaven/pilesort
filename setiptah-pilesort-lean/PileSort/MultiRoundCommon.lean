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

private theorem orient_Q_lt_iff {n : Nat}
    (f : Fin n → Fin n) (s t : Fin n) :
    orient .Q f s < orient .Q f t ↔ f s < f t := by
  simp [orient]

private theorem orient_S_lt_iff {n : Nat}
    (f : Fin n → Fin n) (s t : Fin n) :
    orient .S f s < orient .S f t ↔ f t < f s := by
  change Fin.rev (f s) < Fin.rev (f t) ↔ f t < f s
  simp [Fin.lt_def, Fin.val_rev]
  omega

/-- Pile-type composition: Q is the identity, S flips. -/
def xorType : PileType → PileType → PileType
  | .Q, p => p
  | .S, p => invertType p

/-- Composing two orientations gives a single orientation at their xorType. -/
theorem orient_comp {n m : Nat} (pt1 pt2 : PileType) (f : Fin n → Fin m) (c : Fin n) :
    orient pt1 (orient pt2 f) c = orient (xorType pt1 pt2) f c := by
  cases pt1 <;> cases pt2 <;> simp [orient, xorType, invertType, Fin.rev_rev]

/-! ## Heterogeneous vector keys -/

/-- Orientation of a single Fin value. -/
def orientFin {m : Nat} (pt : PileType) (v : Fin m) : Fin m :=
  match pt with
  | .Q => v
  | .S => Fin.rev v

/-- A heterogeneous vector: values of types Fin ms[0], Fin ms[1], ... -/
inductive HVec : List Nat → Type
  | nil  : HVec []
  | cons {m : Nat} {ms : List Nat} : Fin m → HVec ms → HVec (m :: ms)

/-- Lexicographic comparison on HVec. -/
def HVec.lt {ms : List Nat} : HVec ms → HVec ms → Prop
  | .nil,        .nil        => False
  | .cons h1 t1, .cons h2 t2 => h1 < h2 ∨ (h1 = h2 ∧ HVec.lt t1 t2)

/-- Apply an orientation uniformly to every component of an HVec. -/
def HVec.orient {ms : List Nat} (pt : PileType) : HVec ms → HVec ms
  | .nil       => .nil
  | .cons h t  => .cons (orientFin pt h) (HVec.orient pt t)

/-- Orienting preserves lex order for Q and reverses it for S. -/
private theorem HVec.orient_lt_iff {ms : List Nat} (pt : PileType) (v w : HVec ms) :
    HVec.lt (HVec.orient pt v) (HVec.orient pt w) ↔
    (pt = .Q ∧ HVec.lt v w) ∨ (pt = .S ∧ HVec.lt w v) := by
  sorry

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

/-- `d` respects the order induced by a key function, compared using the
    relation `r` on key values. -/
def RespectsOrder {n : Nat} {α : Type}
    (d : Deck n) (key : Fin n → α) (r : α → α → Prop) : Prop :=
  ∀ s t : Fin n, d.posOf s < d.posOf t ↔ r (key s) (key t)

/-- Two key/order presentations are equivalent if they induce the same pairwise
    comparison relation on cards.

    This is the main payoff of the key-based approach: once a deck is known to
    respect one key/order pair, any order-equivalent presentation can be used
    instead.  In particular, this is the mechanism that should let the
    `shuffleRound_virtualPileTypes` proof move from the three-term key produced
    by two rounds to the compressed two-term virtual-round key. -/
def SameOrder {n : Nat} {α β : Type}
    (key1 : Fin n → α) (r1 : α → α → Prop)
    (key2 : Fin n → β) (r2 : β → β → Prop) : Prop :=
  ∀ s t : Fin n, r1 (key1 s) (key1 t) ↔ r2 (key2 s) (key2 t)

/-- A deck that respects one key/order pair also respects any order-equivalent
    key/order pair. -/
theorem RespectsOrder.of_sameOrder {n : Nat} {α β : Type}
    {d : Deck n}
    {key1 : Fin n → α} {r1 : α → α → Prop}
    {key2 : Fin n → β} {r2 : β → β → Prop}
    (hrespects : RespectsOrder d key1 r1)
    (hsame : SameOrder key1 r1 key2 r2) :
    RespectsOrder d key2 r2 := by
  intro s t
  exact (hrespects s t).trans (hsame s t)

/-- Two decks that each respect the same key/order pair are equal. -/
theorem deck_eq_of_sameOrder {n : Nat} {α : Type}
    (d1 d2 : Deck n) (key : Fin n → α) (r : α → α → Prop)
    (h1 : RespectsOrder d1 key r) (h2 : RespectsOrder d2 key r) :
    d1 = d2 :=
  deck_eq_of_order_iff d1 d2 (fun s t => (h1 s t).trans (h2 s t).symm)

/-- Binary spec composition should reassociate in the same order as sequential
    shuffle rounds. -/
theorem combinedSpec_assoc {n : Nat}
    (spec1 spec2 spec3 : ShuffleSpec n) :
    combinedSpec (combinedSpec spec1 spec2) spec3 =
    combinedSpec spec1 (combinedSpec spec2 spec3) := by
  sorry -- But it seems like we don't need it...

/-- If a deck respects an HVec key, then after one shuffle round the result
    respects the key with the pile assignment prepended and all components
    oriented by the assigned pile type. -/
theorem shuffleRound_respects_hvec_key {n : Nat} {ms : List Nat} (d : Deck n)
    (key : Fin n → HVec ms)
    (hd : RespectsOrder d key HVec.lt)
    (types : List PileType) (assign : Fin n → Fin types.length) :
    RespectsOrder
      (shuffleRound d types assign)
      (fun c => .cons (assign c) (HVec.orient (types.get (assign c)) (key c)))
      HVec.lt := by
  sorry

/-- If a deck respects lex order on a two-component key (f1, f2), then after
    one shuffle round it respects the lex key obtained by prepending the pile
    assignment and orienting both components by the assigned pile type. -/
private theorem shuffleRound_respects_oriented_key {n a b : Nat} (d : Deck n)
    (f1 : Fin n → Fin a) (f2 : Fin n → Fin b)
    (hd : RespectsOrder d (fun c => (f1 c, f2 c))
            (fun x y => x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)))
    (types : List PileType) (assign : Fin n → Fin types.length) :
    RespectsOrder
      (shuffleRound d types assign)
      (fun c => (assign c, orient (types.get (assign c)) f1 c, orient (types.get (assign c)) f2 c))
      (fun x y => x.1 < y.1 ∨ (x.1 = y.1 ∧
        (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2)))) := by
  sorry

/-- Two rounds of pile shuffle equal one round on virtual pile types with the
    combined assignment. -/
theorem shuffleRound_virtualPileTypes {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    shuffleRound (shuffleRound d pt1 assign1) pt2 assign2 =
    shuffleRound d (virtualPileTypes pt1 pt2) (combinedAssign pt1 pt2 assign1 assign2) := by
  sorry

-- `orient pt` on a monotone function reverses or preserves order per pile type.
private theorem orient_lt_iff {n : Nat} (pt : PileType)
    (f : Fin n → Fin n) (s t : Fin n) :
    orient pt f s < orient pt f t ↔
    (pt = .Q ∧ f s < f t) ∨ (pt = .S ∧ f t < f s) := by
  cases pt
  · simp [orient_Q_lt_iff]
  · simp [orient_S_lt_iff]

/-- One round of pile shuffle respects the lexicographic two-term key:
    first by assigned pile, then by the input deck order oriented by that pile. -/
theorem shuffleRound_respects_key {n : Nat} (d : Deck n)
    (types : List PileType)
    (assign : Fin n → Fin types.length) :
    RespectsOrder
      (shuffleRound d types assign)
      (fun c => (assign c, orient (types.get (assign c)) d.posOf c))
      (fun x y => x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := by
  intro s t
  simp only [shuffleRound_order]
  constructor
  · rintro (h | ⟨heq, horient⟩)
    · exact Or.inl h
    · refine Or.inr ⟨heq, ?_⟩
      rw [← heq]
      exact (orient_lt_iff _ d.posOf s t).mpr horient
  · rintro (h | ⟨heq, horient⟩)
    · exact Or.inl h
    · refine Or.inr ⟨heq, ?_⟩
      rw [← heq] at horient
      exact (orient_lt_iff _ d.posOf s t).mp horient

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
