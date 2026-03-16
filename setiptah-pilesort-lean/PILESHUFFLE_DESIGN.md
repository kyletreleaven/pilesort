# PileShuffle Model Design

## Overview

The pile shuffle model formalizes a single round of pile shuffle sort:
deal a deck of cards into piles, then collect the piles in order.
The central type is `Deck n`, which carries both directions of the deck
permutation to avoid ambiguity at every call site.

## Files

| File | Role |
|------|------|
| `PileSort/Permutations.lean` | Technical lemmas about bijections of `Fin n` |
| `PileSort/PileShuffle.lean` | `Deck n`, lifters, `dealToPile`, `collectPile`, `shuffleRound`, `Sortable` |

## `Permutations.lean`

Pure math infrastructure for bijections of `Fin n`, used by the lifter
correctness proofs in `PileShuffle.lean`:

- `List.indexOf_get` : `l.indexOf (l.get k) = k.val`  (for nodup lists)
- `List.get_indexOf` : `l.get ⟨l.indexOf c, _⟩ = c`  (for nodup lists, c ∈ l)
- `Fin.bijective_of_injective` : an injective `Fin n → Fin n` is bijective
- `Fin.invFun_spec` : existence and uniqueness of a left inverse for an injective `Fin n → Fin n`

## `Deck n` (PileShuffle.lean)

A deck of `n` cards is modeled as a permutation of the set `{0, 1, ..., n-1}`.
Cards are identified by their **sorted rank** — card `c : Fin n` is the card that
belongs at position `c` in sorted order.  A deck state is then an arrangement of
those cards: which card is at each position, and equivalently, where each card sits.

`Deck n` carries both directions of this bijection explicitly:

- `posOf c` — where card `c` currently sits  (the permutation σ)
- `cardAt k` — which card is currently at position `k`  (σ⁻¹)

The sorted deck is `Deck.sorted`: every card `c` sits at position `c`.

A pair of mutually inverse functions:

```lean
structure Deck (n : Nat) where
  posOf  : Fin n → Fin n  -- card value  → position in deck
  cardAt : Fin n → Fin n  -- position    → card value
  left_inv  : ∀ c, cardAt (posOf c) = c
  right_inv : ∀ k, posOf (cardAt k) = k
```

### Standard decks

```lean
-- The sorted deck: card c sits at position c
def Deck.sorted (n : Nat) : Deck n   -- posOf = cardAt = id
```

### Lifters

Two constructors for building a `Deck n` from external representations:

```lean
-- From a sequence in position order (list[k] = card at position k)
def Deck.fromDeckSeq (l : List (Fin n))
    (hnd : l.Nodup) (hlen : l.length = n) : Deck n
-- toCard k = l[k];  toPos c = ⟨l.indexOf c, ...⟩
-- correctness uses List.indexOf_get, List.get_indexOf from Permutations.lean

-- From a positions array (poses[c] = position of card c)
def Deck.fromCardPositions (poses : Fin n → Fin n)
    (hinj : Function.Injective poses) : Deck n
-- toPos = poses;  toCard k = the unique c with poses c = k
-- correctness uses Fin.invFun_spec from Permutations.lean
```

## `PileShuffle.lean`

### `dealToPile`

Cards assigned to pile `p`, in deck order (iterates positions via `d.toCard`):

```lean
def dealToPile (d : Deck n) (assign : Fin n → Fin m) (p : Fin m) : List (Fin n) :=
  (List.finRange n).filterMap (fun k =>
    let c := d.toCard k
    if assign c = p then some c else none)
```

### `collectPile`

```lean
def collectPile (t : PileType) (pile : List α) : List α :=
  match t with
  | .Q => pile          -- FIFO: same order as dealt
  | .S => pile.reverse  -- LIFO: reverse of deal order
```

### `shuffleRound`

Deal all cards, collect each pile, concatenate:

```lean
def shuffleRound (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) : Deck n :=
  Deck.fromDeckSeq
    ((List.finRange types.length).flatMap (fun p =>
      collectPile types[p] (dealToPile d assign p)))
    (by ...)   -- Nodup proof
    (by ...)   -- length = n proof
```

The nodup and length proofs require showing that the collected piles partition
the cards (each card appears in exactly one pile, since `assign` is total).

### `Sortable`

```lean
def Sortable (d : Deck n) (types : List PileType) : Prop :=
  ∃ assign : Fin n → Fin types.length,
    shuffleRound d types assign = Deck.sorted n
```

i.e., there exists a deal assignment such that the shuffle produces the sorted deck.

## Multi-round extension (future)

For `k` rounds with per-round type lists `rounds : List (List PileType)`:

```lean
def shuffleMulti (d : Deck n) (rounds : List (List PileType))
    (assigns : ...) : Deck n
```

The key connecting theorem would be:

```lean
theorem shuffleRound_virtualPileTypes (d : Deck n) (pt1 pt2 : List PileType) ... :
    shuffleRound (shuffleRound d pt1 assign1) pt2 assign2 =
    shuffleRound d (virtualPileTypes pt1 pt2) (combinedAssign assign1 assign2)
```

relating the two-round model to `virtualPileTypes` from `VirtualPileTypes.lean`.
