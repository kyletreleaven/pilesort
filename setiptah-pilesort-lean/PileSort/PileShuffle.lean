/-
  Pile shuffle sort model.

  ## Structure

  The file is layered:

  1. List-level shuffle (`dealToPile`, `collectPile`, `shuffleSeq`) — the
     mechanics of pile shuffle on a plain list, with no permutation invariants
     required.  Correctness lemmas (Nodup, length, membership, disjointness)
     live here.

  2. `Deck n` — the permutation type, with constructors and standard decks.
     Cards are identified by sorted rank: card c belongs at position c.
     A Deck carries both directions of the permutation:
       · posOf  c = position of card c  (the permutation σ)
       · cardAt k = card at position k  (σ⁻¹)

  3. `shuffleRound` — lifts `shuffleSeq` to `Deck n` via `Deck.toList` and
     `Deck.fromDeckSeq`.  The proof obligations are discharged by the list-level
     lemmas (TODO: `shuffleSeq_nodup`, `shuffleSeq_length`).

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
import PileSort.CatOrder

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

/-- One pile-shuffle pass on a plain list: deal into piles, collect, concatenate. -/
def shuffleSeq {n : Nat} (l : List (Fin n)) (types : List PileType)
    (assign : Fin n → Fin types.length) : List (Fin n) :=
  (List.finRange types.length).flatMap (fun p =>
    collectPile (types.get p) (dealToPile l assign p))

/-! ### Basic properties -/

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

theorem mem_collectPile {α : Type} (t : PileType) (pile : List α) (a : α) :
    a ∈ collectPile t pile ↔ a ∈ pile := by
  cases t <;> simp [collectPile]

theorem mem_shuffleSeq {n : Nat} (l : List (Fin n)) (types : List PileType)
    (assign : Fin n → Fin types.length) (c : Fin n) :
    c ∈ shuffleSeq l types assign ↔ c ∈ l := by
  simp only [shuffleSeq, List.mem_flatMap, mem_collectPile, mem_dealToPile]
  constructor
  · rintro ⟨_, _, hc, _⟩; exact hc
  · intro hc
    exact ⟨assign c, Fin.mem_of_nodup_length (nodup_finRange _) (by simp) _, hc, rfl⟩

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
    exact getElem_indexOf hmem
  right_inv k := Fin.ext (indexOf_getElem hnd k.val (hlen.symm ▸ k.isLt))

/-- Build a Deck from a positions array (poses c = position of card c).
    Requires poses to be injective (hence bijective, since Fin n is finite). -/
def Deck.fromCardPositions {n : Nat} (poses : Fin n → Fin n)
    (hinj : Injective poses) : Deck n where
  posOf     := poses
  cardAt    := Fin.invOf hinj
  left_inv  := Fin.invOf_left hinj
  right_inv := Fin.invOf_right hinj

/-- cardAt is injective: distinct positions hold distinct cards. -/
theorem Deck.cardAt_injective {n : Nat} (d : Deck n) : Injective d.cardAt :=
  fun a b h => by have := d.right_inv a; rw [h, d.right_inv b] at this; exact this.symm

/-- The position-order sequence of cards in a deck. -/
def Deck.toList {n : Nat} (d : Deck n) : List (Fin n) :=
  (List.finRange n).map d.cardAt

theorem Deck.toList_nodup {n : Nat} (d : Deck n) : d.toList.Nodup :=
  (nodup_finRange n).map (f := d.cardAt) (fun _a _b hne heq => hne (d.cardAt_injective heq))

theorem Deck.toList_length {n : Nat} (d : Deck n) : d.toList.length = n := by
  simp [Deck.toList]

theorem Deck.mem_toList {n : Nat} (d : Deck n) (c : Fin n) : c ∈ d.toList :=
  Fin.mem_of_nodup_length d.toList_nodup d.toList_length c

/-- One round of pile shuffle on a Deck: lifts shuffleSeq via Deck.toList. -/
def shuffleRound {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) : Deck n :=
  Deck.fromDeckSeq (shuffleSeq d.toList types assign)
    (shuffleSeq_nodup d.toList d.toList_nodup types assign)
    ((shuffleSeq_length d.toList types assign).trans d.toList_length)

/-! ## Higher-level results -/

/-- The position of card s in d.toList equals (d.posOf s).val. -/
theorem Deck.toList_indexOf {n : Nat} (d : Deck n) (s : Fin n) :
    d.toList.indexOf s = (d.posOf s).val := by
  have hlt : (d.posOf s).val < d.toList.length := by
    rw [d.toList_length]; exact (d.posOf s).isLt
  have hget : d.toList[(d.posOf s).val]'hlt = s := by
    simp only [Deck.toList, List.getElem_map, List.getElem_finRange]
    exact d.left_inv s
  calc d.toList.indexOf s
      = d.toList.indexOf (d.toList[(d.posOf s).val]'hlt) := by rw [hget]
    _ = (d.posOf s).val := indexOf_getElem d.toList_nodup (d.posOf s).val hlt

/-
  List-level version of shuffleRound_order: order in shuffleSeq output
  is determined by pile assignment and pile type.

  Proof outline:

  1. Membership. Establish hs_f : s ∈ dealToPile l assign (assign s) via mem_dealToPile +
     Fin.mem_of_nodup_length; similarly ht_f for t. Keep these in dealToPile form throughout.

  2. Apply indexOf_flatMap_order. shuffleSeq is definitionally
     (finRange types.length).flatMap (fun p => collectPile (types.get p) (dealToPile l assign p)),
     so `rw [show shuffleSeq ... = flatMap ... from rfl]` exposes this. Then
     `rw [indexOf_flatMap_order ...]` rewrites the goal to:
       (assign s < assign t ∨ assign s = assign t ∧ (pile at assign s).idx s < ... .idx t)
       ↔ (assign s < assign t ∨ ∃ _ : assign s = assign t, Q-or-S)

  3. Bridge ∧ vs ∃. constructor; both directions: the assign s < assign t arm passes
     through; the inner arm uses rintro ⟨heq, hlt⟩ / refine ⟨heq, ?_⟩. Derive
     ht_f' : t ∈ dealToPile l assign (assign s) by rw [heq]; exact ht_f.

  4. Case-split on pile type. `cases htp : types.get (assign s)` adds htp to context but
     does NOT substitute in hlt (only in the goal). Use `simp only [htp, collectPile] at hlt`
     to reduce hlt to dealToPile form (Q) or dealToPile.reverse form (S). Do NOT add dealToPile
     to the simp set — that would unfold to l.filter and break indexOf_reverse_lt's pattern match.

     Q branch: hlt : (dealToPile ...).idx s < (dealToPile ...).idx t.
       Apply (indexOf_filter_lt hs_f ht_f').mp hlt. Lean unfolds dealToPile at semireducible
       level to infer f; the type checker accepts hlt in dealToPile form via definitional equality.

     S branch: hlt : (dealToPile ...).reverse.idx s < (dealToPile ...).reverse.idx t.
       Apply (indexOf_reverse_lt (dealToPile_nodup ...) hs_f ht_f').mp hlt to get
       (dealToPile ...).idx t < (dealToPile ...).idx s. Then apply
       (indexOf_filter_lt ht_f' hs_f).mp to get l.idx t < l.idx s.
       Term-mode .mp uses the type checker, which accepts dealToPile/l.filter via definitional eq.

     Backward direction is symmetric.
-/
/-- The indexOf order within a collected pile reduces to the original list order,
    mediated by pile type: Q preserves order, S reverses it. -/
private theorem collectPile_indexOf_iff {n : Nat} (l : List (Fin n)) (hl : l.Nodup)
    (types : List PileType) (assign : Fin n → Fin types.length) (p : Fin types.length)
    {s t : Fin n} (hs : s ∈ dealToPile l assign p) (ht : t ∈ dealToPile l assign p) :
    (collectPile (types.get p) (dealToPile l assign p)).indexOf s <
    (collectPile (types.get p) (dealToPile l assign p)).indexOf t ↔
      (types.get p = .Q ∧ l.indexOf s < l.indexOf t) ∨
      (types.get p = .S ∧ l.indexOf t < l.indexOf s) := by
  sorry

/-
  Both lemmas work with:
    piles p  = collectPile (types.get p) (dealToPile l assign p)
    lists    = (finRange types.length).map piles
  so that shuffleSeq l types assign = lists.flatten, and lists[p.val] = piles p
  by getElem_map + getElem_finRange.  Membership: s ∈ lists[(assign s).val], etc.
-/

/-- When s and t are dealt to different piles, their order in the shuffleSeq output
    equals the pile assignment order. -/
private theorem shuffleSeq_order_diff {n : Nat} (l : List (Fin n)) (hl : l.Nodup)
    (hlen : l.length = n) (types : List PileType) (assign : Fin n → Fin types.length)
    (s t : Fin n) (hne : assign s ≠ assign t) :
    (shuffleSeq l types assign).indexOf s < (shuffleSeq l types assign).indexOf t ↔
      assign s < assign t := by
  let piles := fun p : Fin types.length => collectPile (types.get p) (dealToPile l assign p)
  let lists := (List.finRange types.length).map piles
  have hseq : shuffleSeq l types assign = lists.flatten := by
    simp only [shuffleSeq, lists]; rfl
  have hlists_len : lists.length = types.length := by simp [lists]
  have hs_lt : (assign s).val < lists.length := hlists_len.symm ▸ (assign s).isLt
  have ht_lt : (assign t).val < lists.length := hlists_len.symm ▸ (assign t).isLt
  have hs : s ∈ lists[(assign s).val]'hs_lt := by
    simp only [lists, List.getElem_map, List.getElem_finRange, Fin.eta]
    exact (mem_collectPile _ _ s).mpr ((mem_dealToPile l assign (assign s) s).mpr
      ⟨Fin.mem_of_nodup_length hl hlen s, rfl⟩)
  have ht : t ∈ lists[(assign t).val]'ht_lt := by
    simp only [lists, List.getElem_map, List.getElem_finRange, Fin.eta]
    exact (mem_collectPile _ _ t).mpr ((mem_dealToPile l assign (assign t) t).mpr
      ⟨Fin.mem_of_nodup_length hl hlen t, rfl⟩)
  have hnd : lists.flatten.Nodup := hseq ▸ shuffleSeq_nodup l hl types assign
  have hval_ne : (assign s).val ≠ (assign t).val := fun h => hne (Fin.ext h)
  rw [hseq]
  constructor
  · intro hlt
    rcases Nat.lt_or_gt_of_ne hval_ne with h | h
    · exact h
    · have := indexOf_flatten_of_lt_val lists hnd ht_lt hs_lt h ht hs
      omega
  · exact fun h => indexOf_flatten_of_lt_val lists hnd hs_lt ht_lt h hs ht

/-- When s and t are dealt to the same pile p, their order in the shuffleSeq output
    is determined by collectPile_indexOf_iff: Q preserves l-order, S reverses it. -/
private theorem shuffleSeq_order_same {n : Nat} (l : List (Fin n)) (hl : l.Nodup)
    (hlen : l.length = n) (types : List PileType) (assign : Fin n → Fin types.length)
    (s t : Fin n) (heq : assign s = assign t) :
    (shuffleSeq l types assign).indexOf s < (shuffleSeq l types assign).indexOf t ↔
      (types.get (assign s) = .Q ∧ l.indexOf s < l.indexOf t) ∨
      (types.get (assign s) = .S ∧ l.indexOf t < l.indexOf s) := by
  -- Rewrite shuffleSeq as lists.flatten.  Use indexOf_flatten_same_val to reduce to the
  -- within-pile comparison, then apply collectPile_indexOf_iff with
  -- hs_f : s ∈ dealToPile l assign (assign s) and ht_f : t ∈ dealToPile l assign (assign s)
  -- (recast via heq).
  sorry

theorem shuffleSeq_order {n : Nat} (l : List (Fin n)) (hl : l.Nodup) (hlen : l.length = n)
    (types : List PileType) (assign : Fin n → Fin types.length) (s t : Fin n) :
    (shuffleSeq l types assign).indexOf s < (shuffleSeq l types assign).indexOf t ↔
      assign s < assign t ∨
      ∃ _ : assign s = assign t,
        (types.get (assign s) = .Q ∧ l.indexOf s < l.indexOf t) ∨
        (types.get (assign s) = .S ∧ l.indexOf t < l.indexOf s) := by
  by_cases heq : assign s = assign t
  · rw [shuffleSeq_order_same l hl hlen types assign s t heq]
    constructor
    · exact fun h => Or.inr ⟨heq, h⟩
    · rintro (h | ⟨_, hQS⟩)
      · exact absurd heq (Fin.ne_of_lt h)
      · exact hQS
  · rw [shuffleSeq_order_diff l hl hlen types assign s t heq]
    constructor
    · exact Or.inl
    · rintro (h | ⟨heq', _⟩)
      · exact h
      · exact absurd heq' heq

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
  simp only []
  -- Unfold posOf: fromDeckSeq.posOf c = ⟨indexOf c, ...⟩, and Fin < is val <
  change (shuffleSeq d.toList types assign).indexOf s <
         (shuffleSeq d.toList types assign).indexOf t ↔ _
  rw [shuffleSeq_order d.toList d.toList_nodup d.toList_length]
  -- Replace d.toList.indexOf with (d.posOf ·).val; Fin < is val < by Fin.lt_def
  simp only [Deck.toList_indexOf, Fin.lt_def]

/-- A deck is sortable in one round with a given pile-type list if there exists
    a deal assignment such that the shuffle round produces the sorted deck. -/
def Sortable {n : Nat} (d : Deck n) (types : List PileType) : Prop :=
  ∃ assign : Fin n → Fin types.length,
    shuffleRound d types assign = Deck.sorted n
