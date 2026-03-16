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
