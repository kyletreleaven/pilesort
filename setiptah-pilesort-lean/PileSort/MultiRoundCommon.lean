import PileSort.Reduction.ShuffleMatchingChain.ChangeProfiles
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

/-- Composing two orientations gives a single orientation at their xorType. -/
theorem orient_comp {n m : Nat} (pt1 pt2 : PileType) (f : Fin n → Fin m) (c : Fin n) :
    orient pt1 (orient pt2 f) c = orient (xorType pt1 pt2) f c := by
  cases pt1 <;> cases pt2 <;> simp [orient, xorType, invertType, Fin.rev_rev]

/-! ## Mixed-radix keys -/

/-- A mixed-radix number: values of types Fin ms[0], Fin ms[1], ...
    Each "digit" lives in a `Fin` whose bound is the corresponding entry of `ms`. -/
inductive Radix : List Nat → Type
  | nil  : Radix []
  | cons {m : Nat} {ms : List Nat} : Fin m → Radix ms → Radix (m :: ms)

infixr:67 " ::r " => Radix.cons

/-- Lexicographic comparison on Radix. -/
def Radix.lt {ms : List Nat} : Radix ms → Radix ms → Prop
  | .nil,      .nil      => False
  | h1 ::r t1, h2 ::r t2 => h1 < h2 ∨ (h1 = h2 ∧ Radix.lt t1 t2)

/-- Apply an orientation uniformly to every digit of a Radix number. -/
def Radix.orient {ms : List Nat} (pt : PileType) : Radix ms → Radix ms
  | .nil    => .nil
  | h ::r t => (orientFin pt h) ::r (Radix.orient pt t)

private theorem Radix.orient_Q_id {ms : List Nat} (v : Radix ms) : Radix.orient .Q v = v := by
  induction v with
  | nil => rfl
  | cons h t ih => simp [Radix.orient, orientFin, ih]

private theorem Radix.orient_S_lt_iff {ms : List Nat} (v w : Radix ms) :
    Radix.lt (Radix.orient .S v) (Radix.orient .S w) ↔ Radix.lt w v := by
  induction v with
  | nil => cases w; simp [Radix.orient, Radix.lt]
  | cons hv tv ih =>
    cases w with
    | cons hw tw =>
      simp only [Radix.orient, Radix.lt, orientFin]
      constructor
      · rintro (h | ⟨heq, hrest⟩)
        · exact Or.inl (by simp [Fin.lt_def, Fin.val_rev] at h; omega)
        · exact Or.inr ⟨Fin.ext (by have := congrArg Fin.val heq; simp [Fin.val_rev] at this; omega),
                        (ih tw).mp hrest⟩
      · rintro (h | ⟨heq, hrest⟩)
        · exact Or.inl (by simp [Fin.lt_def, Fin.val_rev]; omega)
        · exact Or.inr ⟨Fin.ext (by simp [Fin.val_rev, heq]), (ih tw).mpr hrest⟩

/-- Orienting preserves lex order for Q and reverses it for S. -/
private theorem Radix.orient_lt_iff {ms : List Nat} (pt : PileType) (v w : Radix ms) :
    Radix.lt (Radix.orient pt v) (Radix.orient pt w) ↔
    (pt = .Q ∧ Radix.lt v w) ∨ (pt = .S ∧ Radix.lt w v) := by
  cases pt <;> simp [Radix.orient_Q_id, Radix.orient_S_lt_iff]

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
        simp [d1.right_inv]
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

/-- Shared arithmetic step: one block advance covers all offsets. -/
private theorem block_step {b : Nat} (k k' : Nat) (h : k < k') : k * b + b ≤ k' * b :=
  calc k * b + b = k.succ * b := (Nat.succ_mul k b).symm
    _ ≤ k' * b := Nat.mul_le_mul_right b h

/-- Mixed-radix block encoding: `k * b + j < k' * b + j'` iff the block index
    is smaller, or the blocks are equal and the offset is smaller. -/
private theorem block_lt_iff {b : Nat} (k k' : Nat) (j j' : Fin b) :
    k * b + j.val < k' * b + j'.val ↔ k < k' ∨ (k = k' ∧ j < j') := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k k' with hlt | hge
    · exact Or.inl hlt
    · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · exact Or.inr ⟨rfl, by simpa [Fin.lt_def] using h⟩
      · exact absurd h (by
          have hs : k' * b + b ≤ k * b := block_step k' k hgt
          have := j'.isLt; omega)
  · rintro (hlt | ⟨rfl, hlt⟩)
    · have hs : k * b + b ≤ k' * b := block_step k k' hlt
      have := j'.isLt; omega
    · simpa [Fin.lt_def] using hlt

/-- Mixed-radix block encoding: equal encoded values imply equal block and offset. -/
private theorem block_eq_iff {b : Nat} (k k' : Nat) (j j' : Fin b) :
    k * b + j.val = k' * b + j'.val ↔ k = k' ∧ j = j' := by
  constructor
  · intro h
    rcases Nat.lt_or_ge k k' with hlt | hge
    · exact absurd h (by
        have hs : k * b + b ≤ k' * b := block_step k k' hlt
        have := j.isLt; omega)
    · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
      · exact ⟨rfl, Fin.ext (by omega)⟩
      · exact absurd h (by
          have hs : k' * b + b ≤ k * b := block_step k' k hgt
          have := j'.isLt; omega)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Block-encoding the two leading Radix digits preserves lex order (as a SameOrder).
    Used to collapse the first two digits of the two-round key into `combinedAssign`. -/
private theorem Radix.sameOrder_combine_leading {n pa pb : Nat} {ms : List Nat}
    (a : Fin n → Fin pa) (b : Fin n → Fin pb) (rest : Fin n → Radix ms) :
    SameOrder
      (fun c => a c ::r b c ::r rest c) Radix.lt
      (fun c => (⟨a c * pb + b c, block_index_bound (a c).isLt (b c).isLt⟩ : Fin (pa * pb)) ::r rest c) Radix.lt := by
  intro s t
  simp only [Radix.lt, Fin.lt_def, Fin.ext_iff]
  rw [block_lt_iff (a s).val (a t).val (b s) (b t),
      block_eq_iff (a s).val (a t).val (b s) (b t)]
  simp only [Fin.lt_def, Fin.ext_iff]
  constructor
  · rintro (h | ⟨heq, h | ⟨heq2, hrest⟩⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr ⟨heq, h⟩)
    · exact Or.inr ⟨⟨heq, heq2⟩, hrest⟩
  · rintro ((h | ⟨heq, h⟩) | ⟨⟨heq, heq2⟩, hrest⟩)
    · exact Or.inl h
    · exact Or.inr ⟨heq, Or.inl h⟩
    · exact Or.inr ⟨heq, Or.inr ⟨heq2, hrest⟩⟩

/-- If a deck respects a Radix key, then after one shuffle round the result
    respects the key with the pile assignment prepended and all digits
    oriented by the assigned pile type. -/
theorem shuffleRound_respects_radix_key {n : Nat} {ms : List Nat} (d : Deck n)
    (key : Fin n → Radix ms)
    (hd : RespectsOrder d key Radix.lt)
    (types : List PileType) (assign : Fin n → Fin types.length) :
    RespectsOrder
      (shuffleRound d types assign)
      (fun c => (assign c) ::r (Radix.orient (types.get (assign c)) (key c)))
      Radix.lt := by
  intro s t
  simp only [shuffleRound_order, Radix.lt]
  constructor
  · rintro (h | ⟨heq, hcase⟩)
    · exact Or.inl h
    · refine Or.inr ⟨heq, ?_⟩
      rw [← heq, Radix.orient_lt_iff]
      rcases hcase with ⟨hQ, hlt⟩ | ⟨hS, hlt⟩
      · exact Or.inl ⟨hQ, (hd s t).mp hlt⟩
      · exact Or.inr ⟨hS, (hd t s).mp hlt⟩
  · rintro (h | ⟨heq, hlt⟩)
    · exact Or.inl h
    · refine Or.inr ⟨heq, ?_⟩
      rw [← heq] at hlt
      rw [Radix.orient_lt_iff] at hlt
      rcases hlt with ⟨hQ, hlt⟩ | ⟨hS, hlt⟩
      · exact Or.inl ⟨hQ, (hd s t).mpr hlt⟩
      · exact Or.inr ⟨hS, (hd t s).mpr hlt⟩

-- `orient` and `orientFin` are the same operation: orient pt f c = orientFin pt (f c).
private theorem orientFin_eq_orient {n m : Nat} (pt : PileType) (f : Fin n → Fin m) (c : Fin n) :
    orientFin pt (f c) = orient pt f c := by
  cases pt <;> rfl

/-- A deck respects its own position function as a singleton Radix key.
    This is the trivial starting point for the key-chain argument. -/
theorem deck_respects_posOf {n : Nat} (d : Deck n) :
    RespectsOrder d (fun c => d.posOf c ::r .nil) Radix.lt := by
  intro s t; simp [Radix.lt]

/-- One shuffle round respects a two-digit Radix key: pile assignment followed by
    the input deck position oriented by the assigned pile type. -/
theorem oneShuffleRound_respects_key {n : Nat} (d : Deck n)
    (types : List PileType) (assign : Fin n → Fin types.length) :
    RespectsOrder
      (shuffleRound d types assign)
      (fun c => assign c ::r orient (types.get (assign c)) d.posOf c ::r .nil)
      Radix.lt :=
  (shuffleRound_respects_radix_key d _ (deck_respects_posOf d) types assign).of_sameOrder
    (fun s t => by simp [Radix.orient, orientFin_eq_orient])

/-- Two shuffle rounds respect a three-digit Radix key: outer pile assignment,
    inner pile assignment oriented by outer pile type, and deck position oriented
    by the composed pile types. -/
theorem twoShuffleRound_respects_key {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    RespectsOrder
      (shuffleRound (shuffleRound d pt1 assign1) pt2 assign2)
      (fun c =>
        assign2 c ::r
        orient (pt2.get (assign2 c)) assign1 c ::r
        orient (xorType (pt2.get (assign2 c)) (pt1.get (assign1 c))) d.posOf c ::r
        .nil)
      Radix.lt :=
  (shuffleRound_respects_radix_key _ _ (oneShuffleRound_respects_key d pt1 assign1) pt2 assign2).of_sameOrder
    (fun s t => by simp [Radix.orient, orientFin_eq_orient, orient_comp])

/-- Two shuffle rounds respect a two-digit Radix key with the first two digits
    of the three-digit key collapsed via block encoding. -/
theorem twoShuffleRound_respects_combined_key {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    RespectsOrder
      (shuffleRound (shuffleRound d pt1 assign1) pt2 assign2)
      (fun c =>
        ⟨(assign2 c).val * pt1.length + (orient (pt2.get (assign2 c)) assign1 c).val,
         block_index_bound (assign2 c).isLt (orient (pt2.get (assign2 c)) assign1 c).isLt⟩ ::r
        orient (xorType (pt2.get (assign2 c)) (pt1.get (assign1 c))) d.posOf c ::r
        .nil)
      Radix.lt :=
  (twoShuffleRound_respects_key d pt1 pt2 assign1 assign2).of_sameOrder
    (Radix.sameOrder_combine_leading assign2
      (fun c => orient (pt2.get (assign2 c)) assign1 c)
      (fun c => orient (xorType (pt2.get (assign2 c)) (pt1.get (assign1 c))) d.posOf c ::r .nil))

/-- The virtual pile type at the combined index equals the xor of the two component
    pile types.  This is the core identity of the virtual pile type theory. -/
theorem virtualPileTypes_get_combinedAssign {n : Nat} (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length) (assign2 : Fin n → Fin pt2.length) (c : Fin n) :
    (virtualPileTypes pt1 pt2).get (combinedAssign pt1 pt2 assign1 assign2 c) =
    xorType (pt2.get (assign2 c)) (pt1.get (assign1 c)) := by
  simp only [List.get_eq_getElem, combinedAssign, ← orientFin_eq_orient]
  have hk := (assign2 c).isLt
  have hj := (orientFin (pt2.get (assign2 c)) (assign1 c)).isLt
  exact (virtualPileTypes_getElem pt1 pt2 (assign2 c).val
      (orientFin (pt2.get (assign2 c)) (assign1 c)).val hk hj
      (by rw [virtualPileTypes_length]; exact block_index_bound hk hj)).trans
    (applyPile_orient_getElem (pt2.get (assign2 c)) pt1 (assign1 c))

/-- Two shuffle rounds respect the same key as one virtual round:
    `combinedAssign` followed by the virtual pile type orientation. -/
theorem twoShuffleRound_respects_virtualKey {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    RespectsOrder
      (shuffleRound (shuffleRound d pt1 assign1) pt2 assign2)
      (fun c =>
        combinedAssign pt1 pt2 assign1 assign2 c ::r
        orient ((virtualPileTypes pt1 pt2).get (combinedAssign pt1 pt2 assign1 assign2 c))
               d.posOf c ::r
        .nil)
      Radix.lt :=
  (twoShuffleRound_respects_combined_key d pt1 pt2 assign1 assign2).of_sameOrder
    (fun s t => by
      rw [virtualPileTypes_get_combinedAssign, virtualPileTypes_get_combinedAssign]
      simp [Radix.lt, Fin.lt_def, Fin.ext_iff, combinedAssign, orientFin_eq_orient])

/-- Two rounds of pile shuffle equal one round on virtual pile types with the
    combined assignment. -/
theorem shuffleRound_virtualPileTypes {n : Nat} (d : Deck n)
    (pt1 pt2 : List PileType)
    (assign1 : Fin n → Fin pt1.length)
    (assign2 : Fin n → Fin pt2.length) :
    shuffleRound (shuffleRound d pt1 assign1) pt2 assign2 =
    shuffleRound d (virtualPileTypes pt1 pt2) (combinedAssign pt1 pt2 assign1 assign2) :=
  deck_eq_of_sameOrder _ _ _ _
    (twoShuffleRound_respects_virtualKey d pt1 pt2 assign1 assign2)
    (oneShuffleRound_respects_key d (virtualPileTypes pt1 pt2)
      (combinedAssign pt1 pt2 assign1 assign2))

/-- Virtual pile type composition should reassociate in the same order as
    sequential shuffle rounds.  This is recorded here as a potential algebraic
    helper for future-oriented fold proofs. -/
theorem virtualPileTypes_assoc (pt1 pt2 pt3 : List PileType) :
    virtualPileTypes (virtualPileTypes pt1 pt2) pt3 =
    virtualPileTypes pt1 (virtualPileTypes pt2 pt3) := by
  induction pt3 with
  | nil => simp [virtualPileTypes]
  | cons t rest ih =>
    show applyPile t (virtualPileTypes pt1 pt2) ++ virtualPileTypes (virtualPileTypes pt1 pt2) rest =
         virtualPileTypes pt1 (applyPile t pt2 ++ virtualPileTypes pt2 rest)
    rw [applyPile_virtualPileTypes, ih, ← virtualPileTypes_append]

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
  let split := fun c => splitAssign pt1 pt2 ((spec.assign c).cast (by simp [h]))
  ( { types := pt1
      assign := fun c => (split c).1 }
  , { types := pt2
      assign := fun c => (split c).2 } )

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

/-- Splitting a combined spec and recombining the two recovered component specs
    gives back the original combined spec. -/
theorem combinedSpec_splitSpec {n : Nat}
    (spec : ShuffleSpec n) (pt1 pt2 : List PileType)
    (h : spec.types = virtualPileTypes pt1 pt2) :
    combinedSpec (splitSpec spec pt1 pt2 h).1 (splitSpec spec pt1 pt2 h).2 = spec := by
  cases spec with
  | mk spec_types spec_assign =>
    simp only at h
    subst h
    show combinedSpec
        { types := pt1, assign := fun c => (splitAssign pt1 pt2 (spec_assign c)).1 }
        { types := pt2, assign := fun c => (splitAssign pt1 pt2 (spec_assign c)).2 } =
        { types := virtualPileTypes pt1 pt2, assign := spec_assign }
    simp only [combinedSpec]
    congr 1
    funext c
    exact (combinedAssign_congr pt1 pt2
        (fun c' => (splitAssign pt1 pt2 (spec_assign c')).1)
        (fun _ => (splitAssign pt1 pt2 (spec_assign c)).1)
        (fun c' => (splitAssign pt1 pt2 (spec_assign c')).2)
        (fun _ => (splitAssign pt1 pt2 (spec_assign c)).2)
        c rfl rfl).trans
      (combinedAssign_split pt1 pt2 (spec_assign c) c)

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
