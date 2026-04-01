import PileSort.PileTypes
import PileSort.Lists
import PileSort.Permutations
import PileSort.CatOrder

/-! ## List-level pile shuffle -/

/-- Cards in list `l` assigned to pile `p`, in the order they appear in `l`. -/
def dealToPile {n m : Nat} (l : List (Fin n)) (assign : Fin n → Fin m) (p : Fin m) :
    List (Fin n) :=
  l.filter (fun c => assign c = p)

/-- Collect a pile: queue preserves order; stack reverses it. -/
def collectPile {α : Type} (t : PileType) (pile : List α) : List α :=
  match t with
  | .Q => pile
  | .S => pile.reverse

/-- One pile-shuffle pass on a plain list: deal into piles, collect, concatenate. -/
def shuffleSeq {n : Nat} (l : List (Fin n)) (types : List PileType)
    (assign : Fin n → Fin types.length) : List (Fin n) :=
  (List.finRange types.length).flatMap (fun p =>
    collectPile (types.get p) (dealToPile l assign p))

theorem collectPile_length {α : Type} (t : PileType) (pile : List α) :
    (collectPile t pile).length = pile.length := by
  cases t <;> simp [collectPile]

theorem collectPile_nodup {α : Type} (t : PileType) (pile : List α) :
    (collectPile t pile).Nodup ↔ pile.Nodup := by
  cases t <;> simp [collectPile, List.Nodup, List.pairwise_reverse, Ne, eq_comm]

theorem dealToPile_nodup {n m : Nat} (l : List (Fin n)) (hl : l.Nodup)
    (assign : Fin n → Fin m) (p : Fin m) : (dealToPile l assign p).Nodup :=
  hl.filter _

theorem collectPile_perm {α : Type} (t : PileType) (pile : List α) :
    List.Perm (collectPile t pile) pile := by
  cases t <;> simp [collectPile]

theorem shuffleSeq_perm {n : Nat} (l : List (Fin n)) (types : List PileType)
    (assign : Fin n → Fin types.length) : List.Perm (shuffleSeq l types assign) l := by
  simp only [shuffleSeq]
  apply List.Perm.trans
  · apply List.flatMap_perm_congr
    intro p _
    exact collectPile_perm (types.get p) _
  · exact flatMap_filter_perm l assign

theorem shuffleSeq_length {n : Nat} (l : List (Fin n)) (types : List PileType)
    (assign : Fin n → Fin types.length) :
    (shuffleSeq l types assign).length = l.length :=
  (shuffleSeq_perm l types assign).length_eq

theorem shuffleSeq_nodup {n : Nat} (l : List (Fin n)) (hl : l.Nodup) (types : List PileType)
    (assign : Fin n → Fin types.length) : (shuffleSeq l types assign).Nodup :=
  (shuffleSeq_perm l types assign).nodup_iff.mpr hl

/-! ## Deck and single-round sortability -/

@[ext]
structure Deck (n : Nat) where
  posOf  : Fin n → Fin n
  cardAt : Fin n → Fin n
  left_inv  : ∀ c, cardAt (posOf c) = c
  right_inv : ∀ k, posOf (cardAt k) = k

def Deck.sorted (n : Nat) : Deck n where
  posOf     := id
  cardAt    := id
  left_inv  := fun _ => rfl
  right_inv := fun _ => rfl

def Deck.fromDeckSeq {n : Nat} (l : List (Fin n))
    (hnd : l.Nodup) (hlen : l.length = n) : Deck n where
  cardAt    := l.get ∘ Fin.cast hlen.symm
  posOf  c  := ⟨l.indexOf c,
                Nat.lt_of_lt_of_eq
                  (indexOf_lt_length (Fin.mem_of_nodup_length hnd hlen c))
                  hlen⟩
  left_inv  c := by
    have hmem := Fin.mem_of_nodup_length hnd hlen c
    exact getElem_indexOf hmem
  right_inv k := Fin.ext (indexOf_getElem hnd k.val (hlen.symm ▸ k.isLt))

def Deck.fromCardPositions {n : Nat} (poses : Fin n → Fin n)
    (hinj : Injective poses) : Deck n where
  posOf     := poses
  cardAt    := Fin.invOf hinj
  left_inv  := Fin.invOf_left hinj
  right_inv := Fin.invOf_right hinj

theorem Deck.cardAt_injective {n : Nat} (d : Deck n) : Injective d.cardAt :=
  fun a b h => by have := d.right_inv a; rw [h, d.right_inv b] at this; exact this.symm

def Deck.toList {n : Nat} (d : Deck n) : List (Fin n) :=
  (List.finRange n).map d.cardAt

theorem Deck.toList_nodup {n : Nat} (d : Deck n) : d.toList.Nodup :=
  (nodup_finRange n).map (f := d.cardAt) (fun _a _b hne heq => hne (d.cardAt_injective heq))

theorem Deck.toList_length {n : Nat} (d : Deck n) : d.toList.length = n := by
  simp [Deck.toList]

def shuffleRound {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) : Deck n :=
  Deck.fromDeckSeq (shuffleSeq d.toList types assign)
    (shuffleSeq_nodup d.toList d.toList_nodup types assign)
    ((shuffleSeq_length d.toList types assign).trans d.toList_length)

def Sortable {n : Nat} (d : Deck n) (types : List PileType) : Prop :=
  ∃ assign : Fin n → Fin types.length,
    shuffleRound d types assign = Deck.sorted n
