/-
  Pile shuffle sort model.

  A Deck n carries both directions of the deck permutation to avoid
  ambiguity at call sites:
    · posOf  c = position of card c  (the permutation σ)
    · cardAt k = card at position k  (σ⁻¹)

  Cards are identified by sorted rank: card c belongs at position c
  in the sorted deck.
-/
import PileSort.Basic
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

/-- One round of pile shuffle: deal all cards into piles, collect each pile, concatenate.
    Returns the resulting deck sequence (position order).
    The two proof obligations (Nodup, length = n) both follow from the fact that
    `assign` partitions all n cards across the piles: each card lands in exactly one
    pile, so the piles are disjoint and their sizes sum to n.  The proofs require
    infrastructure lemmas ("filterMap of a nodup list with an injective function is
    nodup", "flatMap of disjoint nodup lists is nodup") that are not yet in scope. -/
def shuffleRound {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) : Deck n :=
  Deck.fromDeckSeq
    ((List.finRange types.length).flatMap (fun p =>
      collectPile (types.get p) (dealToPile d assign p)))
    (by sorry)  -- TODO: each card appears in exactly one pile (assign is total)
    (by sorry)  -- TODO: total length = n (assign covers all n cards)

/-- A deck is sortable in one round with a given pile-type list if there exists
    a deal assignment such that the shuffle round produces the sorted deck. -/
def Sortable {n : Nat} (d : Deck n) (types : List PileType) : Prop :=
  ∃ assign : Fin n → Fin types.length,
    shuffleRound d types assign = Deck.sorted n
