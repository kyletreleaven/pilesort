/-
  Pile shuffle sort model.

  A Deck n carries both directions of the deck permutation to avoid
  ambiguity at call sites:
    · posOf  c = position of card c  (the permutation σ)
    · cardAt k = card at position k  (σ⁻¹)

  Cards are identified by sorted rank: card c belongs at position c
  in the sorted deck.

  ## Structure

  The file is layered:

  1. `Deck n` — the permutation type, with constructors and standard decks.

  2. List-level shuffle (`dealToPile`, `collectPile`, `shuffleSeq`) — the
     mechanics of pile shuffle on a plain list, with no permutation invariants
     required.  Correctness lemmas (Nodup, length, membership, disjointness)
     live here.

  3. `shuffleRound` — lifts `shuffleSeq` to `Deck n` via `Deck.toList` and
     `Deck.fromDeckSeq`.  The proof obligations are discharged by the list-level
     lemmas.

  4. `Sortable`, `shuffleRound_order` — higher-level results.

  ## Proof roadmap for `shuffleRound_virtualPileTypes`

  The central target is:

      shuffleRound (shuffleRound d pt1 assign1) pt2 assign2
        = shuffleRound d (virtualPileTypes pt1 pt2) combinedAssign

  Strategy:

  1. Prove `shuffleRound_order`: the output ordering is determined by pile
     assignment and pile type (earlier pile wins; within a pile, Q preserves
     deck order and S reverses it).

  2. Define `combinedAssign`: maps each card to a block-indexed virtual pile,
       combinedAssign c = assign2(c) * pt1.length + f(assign2 c, assign1 c)
     where f adjusts the round-1 index based on whether pt2[assign2 c] is Q
     (identity) or S (reversed block).

  3. Prove `shuffleRound_virtualPileTypes` by Deck extensionality (posOf
     agreement suffices): apply `shuffleRound_order` twice on the LHS and
     once on the RHS, then use `virtualPileTypes_getElem` to match the
     virtual pile type at the combined index to the composed condition.
-/
import PileSort.Basic
import PileSort.Lists
import PileSort.Permutations

/-! ## Deck -/

/-- A deck of n cards: both directions of the permutation, mutually inverse. -/
structure Deck (n : Nat) where
  posOf  : Fin n → Fin n  -- card value  → position in deck
  cardAt : Fin n → Fin n  -- position    → card value
  left_inv  : ∀ c, cardAt (posOf c) = c
  right_inv : ∀ k, posOf (cardAt k) = k

/-- The sorted deck: card c sits at position c. -/
def Deck.sorted (n : Nat) : Deck n where
  posOf     := id
  cardAt    := id
  left_inv  := fun _ => rfl
  right_inv := fun _ => rfl

/-- Build a Deck from a list in position order (l[k] = card at position k).
    Requires l to be Nodup with length n. -/
def Deck.fromDeckSeq {n : Nat} (l : List (Fin n))
    (hnd : l.Nodup) (hlen : l.length = n) : Deck n where
  cardAt    := l.get ∘ Fin.cast hlen.symm
  posOf  c  := ⟨l.indexOf c,
                Nat.lt_of_lt_of_eq
                  (indexOf_lt_length (Fin.mem_of_nodup_length hnd hlen c))
                  hlen⟩
  left_inv  c := by
    have hmem := Fin.mem_of_nodup_length hnd hlen c
    exact getElem_indexOf hnd hmem
  right_inv k := Fin.ext (indexOf_getElem hnd k.val (hlen.symm ▸ k.isLt))

/-- Build a Deck from a positions array (poses c = position of card c).
    Requires poses to be injective (hence bijective, since Fin n is finite).
    Noncomputable because the inverse is constructed via Classical.choice. -/
noncomputable def Deck.fromCardPositions {n : Nat} (poses : Fin n → Fin n)
    (hinj : Injective poses) : Deck n where
  posOf  := poses
  cardAt k := (Fin.invFun_spec hinj k).choose
  left_inv  c := hinj (Fin.invFun_spec hinj (poses c)).choose_spec
  right_inv k := (Fin.invFun_spec hinj k).choose_spec

theorem Deck.cardAt_injective {n : Nat} (d : Deck n) : Injective d.cardAt :=
  fun a b h => by have := d.right_inv a; rw [h, d.right_inv b] at this; exact this.symm

/-- The position-order sequence of cards in a deck. -/
def Deck.toList {n : Nat} (d : Deck n) : List (Fin n) :=
  (List.finRange n).map d.cardAt

theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  simp [List.Nodup, List.pairwise_iff_getElem, Fin.ext_iff, Nat.ne_of_lt]
  omega

theorem Deck.toList_nodup {n : Nat} (d : Deck n) : d.toList.Nodup :=
  (nodup_finRange n).map (f := d.cardAt) (fun a b hne heq => hne (d.cardAt_injective heq))

theorem Deck.toList_length {n : Nat} (d : Deck n) : d.toList.length = n := by
  simp [Deck.toList]

theorem Deck.mem_toList {n : Nat} (d : Deck n) (c : Fin n) : c ∈ d.toList :=
  Fin.mem_of_nodup_length d.toList_nodup d.toList_length c

/-! ## List-level pile shuffle -/

/-- Cards in list l assigned to pile p, in the order they appear in l. -/
def dealToPile {n m : Nat} (l : List (Fin n)) (assign : Fin n → Fin m) (p : Fin m) :
    List (Fin n) :=
  l.filter (fun c => assign c = p)

/-- Collect a pile: Queue (FIFO) preserves order; Stack (LIFO) reverses it. -/
def collectPile {α : Type} (t : PileType) (pile : List α) : List α :=
  match t with
  | .Q => pile
  | .S => pile.reverse

theorem collectPile_length {α : Type} (t : PileType) (pile : List α) :
    (collectPile t pile).length = pile.length := by
  cases t <;> simp [collectPile]

theorem collectPile_nodup {α : Type} (t : PileType) (pile : List α) :
    (collectPile t pile).Nodup ↔ pile.Nodup := by
  cases t <;> simp [collectPile, List.Nodup, List.pairwise_reverse, Ne, eq_comm]

theorem dealToPile_nodup {n m : Nat} (l : List (Fin n)) (hl : l.Nodup)
    (assign : Fin n → Fin m) (p : Fin m) : (dealToPile l assign p).Nodup :=
  hl.filter _

theorem mem_dealToPile {n m : Nat} (l : List (Fin n)) (assign : Fin n → Fin m)
    (p : Fin m) (c : Fin n) : c ∈ dealToPile l assign p ↔ c ∈ l ∧ assign c = p := by
  simp [dealToPile, List.mem_filter]

theorem dealToPile_disjoint {n m : Nat} (l : List (Fin n)) (assign : Fin n → Fin m)
    (p q : Fin m) (c : Fin n) (hp : c ∈ dealToPile l assign p)
    (hq : c ∈ dealToPile l assign q) : p = q := by
  simp [mem_dealToPile] at hp hq; exact hp.2.symm.trans hq.2

/-- One pile-shuffle pass on a plain list: deal into piles, collect, concatenate. -/
def shuffleSeq {n : Nat} (l : List (Fin n)) (types : List PileType)
    (assign : Fin n → Fin types.length) : List (Fin n) :=
  (List.finRange types.length).flatMap (fun p =>
    collectPile (types.get p) (dealToPile l assign p))

/-! ## Lifting to Deck -/

/-- One round of pile shuffle on a Deck: lifts shuffleSeq via Deck.toList. -/
def shuffleRound {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) : Deck n :=
  Deck.fromDeckSeq (shuffleSeq d.toList types assign)
    (by sorry)  -- TODO: shuffleSeq_nodup
    (by sorry)  -- TODO: shuffleSeq_length

/-! ## Higher-level results -/

/-- The order of cards in the output deck is determined by pile assignment and pile type:
    d'.posOf s < d'.posOf t iff
      · assign s < assign t  (s dealt to an earlier pile), or
      · assign s = assign t = x, types[x] = Q, and d.posOf s < d.posOf t  (FIFO), or
      · assign s = assign t = x, types[x] = S, and d.posOf t < d.posOf s  (LIFO). -/
theorem shuffleRound_order {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) (s t : Fin n) :
    let d' := shuffleRound d types assign
    d'.posOf s < d'.posOf t ↔
      assign s < assign t ∨
      ∃ _ : assign s = assign t,
        (types.get (assign s) = .Q ∧ d.posOf s < d.posOf t) ∨
        (types.get (assign s) = .S ∧ d.posOf t < d.posOf s) := by
  sorry

/-- A deck is sortable in one round with a given pile-type list if there exists
    a deal assignment such that the shuffle round produces the sorted deck. -/
def Sortable {n : Nat} (d : Deck n) (types : List PileType) : Prop :=
  ∃ assign : Fin n → Fin types.length,
    shuffleRound d types assign = Deck.sorted n
