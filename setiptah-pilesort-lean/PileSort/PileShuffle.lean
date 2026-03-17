/-
  Pile shuffle sort model.

  A Deck n carries both directions of the deck permutation to avoid
  ambiguity at call sites:
    · posOf  c = position of card c  (the permutation σ)
    · cardAt k = card at position k  (σ⁻¹)

  Cards are identified by sorted rank: card c belongs at position c
  in the sorted deck.

  ## Proof roadmap

  The central target is `shuffleRound_virtualPileTypes`:

      shuffleRound (shuffleRound d pt1 assign1) pt2 assign2
        = shuffleRound d (virtualPileTypes pt1 pt2) combinedAssign

  The strategy:

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

  Prerequisites: the two sorry obligations in `shuffleRound` (Nodup and
  length = n, both following from the partition property of assign) must be
  discharged before `shuffleRound_order` can be proved.
-/
import PileSort.Basic
import PileSort.Lists
import PileSort.Permutations

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

/-- Cards assigned to pile p, listed in deck order (iterating positions via cardAt). -/
def dealToPile {n m : Nat} (d : Deck n) (assign : Fin n → Fin m) (p : Fin m) :
    List (Fin n) :=
  (List.finRange n).filterMap (fun k =>
    let c := d.cardAt k
    if assign c = p then some c else none)

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


theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  simp [List.Nodup, List.pairwise_iff_getElem, Fin.ext_iff, Nat.ne_of_lt]
  omega

theorem Deck.cardAt_injective {n : Nat} (d : Deck n) : Injective d.cardAt :=
  fun a b h => by have := d.right_inv a; rw [h, d.right_inv b] at this; exact this.symm

/-- dealToPile produces a Nodup list. -/
theorem dealToPile_nodup {n m : Nat} (d : Deck n) (assign : Fin n → Fin m) (p : Fin m) :
    (dealToPile d assign p).Nodup := by
  apply List.Nodup.filterMap (nodup_finRange n)
  intro a _ b _ x ha hb
  simp only [Option.ite_none_right_eq_some] at ha hb
  exact d.cardAt_injective (Option.some.inj (ha.2.trans hb.2.symm))

/-- One round of pile shuffle: deal all cards into piles, collect each pile, concatenate.
    Returns the resulting deck sequence (position order).

    The two proof obligations (Nodup, length = n) both follow from the fact that
    `assign` partitions all n cards across the piles: each card lands in exactly one
    pile, so the piles are disjoint and their sizes sum to n.

    Estimated work (~4-6 helper lemmas, a few hours):
      · `collectPile` preserves length and Nodup (trivial)
      · `dealToPile d assign p` is Nodup — filterMap on nodup `finRange n` with
        injective `d.cardAt` (from `right_inv`) keeps values distinct
      · sizes of `dealToPile` sum to n — partition/counting argument, needs
        `List.length_filterMap` or equivalent
      · piles are pairwise disjoint — card c ∈ pile p iff `assign c = p`
      · `flatMap_nodup_of_disjoint` — flatMap of pairwise disjoint nodup lists
        is nodup; the hardest piece, likely not in core -/
def shuffleRound {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) : Deck n :=
  Deck.fromDeckSeq
    ((List.finRange types.length).flatMap (fun p =>
      collectPile (types.get p) (dealToPile d assign p)))
    (by sorry)  -- TODO: each card appears in exactly one pile (assign is total)
    (by sorry)  -- TODO: total length = n (assign covers all n cards)

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
