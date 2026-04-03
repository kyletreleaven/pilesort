import PileSort.Shuffle.Defs

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

theorem collectPile_indexOf_lt {α : Type} [DecidableEq α] (t : PileType) (pile : List α)
    (hnd : pile.Nodup) {a b : α} (ha : a ∈ pile) (hb : b ∈ pile) :
    (collectPile t pile).indexOf a < (collectPile t pile).indexOf b ↔
      (t = .Q ∧ pile.indexOf a < pile.indexOf b) ∨
      (t = .S ∧ pile.indexOf b < pile.indexOf a) := by
  cases t with
  | Q => simp [collectPile]
  | S => simp [collectPile, indexOf_reverse_lt hnd ha hb]

theorem mem_shuffleSeq {n : Nat} (l : List (Fin n)) (types : List PileType)
    (assign : Fin n → Fin types.length) (c : Fin n) :
    c ∈ shuffleSeq l types assign ↔ c ∈ l := by
  simp only [shuffleSeq, List.mem_flatMap, mem_collectPile, mem_dealToPile]
  constructor
  · rintro ⟨_, _, hc, _⟩; exact hc
  · intro hc
    exact ⟨assign c, Fin.mem_of_nodup_length (nodup_finRange _) (by simp) _, hc, rfl⟩

theorem Deck.mem_toList {n : Nat} (d : Deck n) (c : Fin n) : c ∈ d.toList :=
  Fin.mem_of_nodup_length d.toList_nodup d.toList_length c

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

private theorem collectPile_indexOf_iff {n : Nat} (l : List (Fin n)) (hl : l.Nodup)
    (types : List PileType) (assign : Fin n → Fin types.length) (p : Fin types.length)
    {s t : Fin n} (hs : s ∈ dealToPile l assign p) (ht : t ∈ dealToPile l assign p) :
    (collectPile (types.get p) (dealToPile l assign p)).indexOf s <
    (collectPile (types.get p) (dealToPile l assign p)).indexOf t ↔
      (types.get p = .Q ∧ l.indexOf s < l.indexOf t) ∨
      (types.get p = .S ∧ l.indexOf t < l.indexOf s) := by
  rw [collectPile_indexOf_lt _ _ (dealToPile_nodup l hl assign p) hs ht]
  constructor
  · rintro (⟨hQ, h⟩ | ⟨hS, h⟩)
    · exact Or.inl ⟨hQ, (indexOf_filter_lt hs ht).mp h⟩
    · exact Or.inr ⟨hS, (indexOf_filter_lt ht hs).mp h⟩
  · rintro (⟨hQ, h⟩ | ⟨hS, h⟩)
    · exact Or.inl ⟨hQ, (indexOf_filter_lt hs ht).mpr h⟩
    · exact Or.inr ⟨hS, (indexOf_filter_lt ht hs).mpr h⟩

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

private theorem shuffleSeq_order_same {n : Nat} (l : List (Fin n)) (hl : l.Nodup)
    (hlen : l.length = n) (types : List PileType) (assign : Fin n → Fin types.length)
    (s t : Fin n) (heq : assign s = assign t) :
    (shuffleSeq l types assign).indexOf s < (shuffleSeq l types assign).indexOf t ↔
      (types.get (assign s) = .Q ∧ l.indexOf s < l.indexOf t) ∨
      (types.get (assign s) = .S ∧ l.indexOf t < l.indexOf s) := by
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
  have ht' : t ∈ lists[(assign s).val]'hs_lt := by
    simp only [lists, List.getElem_map, List.getElem_finRange, Fin.eta]
    exact (mem_collectPile _ _ t).mpr ((mem_dealToPile l assign (assign s) t).mpr
      ⟨Fin.mem_of_nodup_length hl hlen t, heq.symm⟩)
  have hs_f : s ∈ dealToPile l assign (assign s) :=
    (mem_dealToPile l assign (assign s) s).mpr ⟨Fin.mem_of_nodup_length hl hlen s, rfl⟩
  have ht_f : t ∈ dealToPile l assign (assign s) :=
    (mem_dealToPile l assign (assign s) t).mpr ⟨Fin.mem_of_nodup_length hl hlen t, heq.symm⟩
  rw [hseq, indexOf_flatten_same_val lists hnd hs_lt hs ht']
  simp only [lists, List.getElem_map, List.getElem_finRange, Fin.eta]
  exact collectPile_indexOf_iff l hl types assign (assign s) hs_f ht_f

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

theorem shuffleRound_order {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length) (s t : Fin n) :
    let d' := shuffleRound d types assign
    d'.posOf s < d'.posOf t ↔
      assign s < assign t ∨
      ∃ _ : assign s = assign t,
        (types.get (assign s) = .Q ∧ d.posOf s < d.posOf t) ∨
        (types.get (assign s) = .S ∧ d.posOf t < d.posOf s) := by
  simp only []
  change (shuffleSeq d.toList types assign).indexOf s <
         (shuffleSeq d.toList types assign).indexOf t ↔ _
  rw [shuffleSeq_order d.toList d.toList_nodup d.toList_length]
  simp only [Deck.toList_indexOf, Fin.lt_def]

theorem shuffleRound_consecutive {n : Nat} (d : Deck n) (types : List PileType)
    (assign : Fin n → Fin types.length)
    (s : Fin n) (hs : s.val + 1 < n) :
    let s' : Fin n := ⟨s.val + 1, hs⟩
    (shuffleRound d types assign).posOf s < (shuffleRound d types assign).posOf s' ↔
    assign s < assign s' ∨
    assign s = assign s' ∧
      ((types.get (assign s) = .Q ∧ d.posOf s < d.posOf s') ∨
       (types.get (assign s) = .S ∧ d.posOf s' < d.posOf s)) := by
  let s' : Fin n := ⟨s.val + 1, hs⟩
  constructor
  · intro h
    rcases (shuffleRound_order d types assign s s').mp h with h | ⟨heq, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨heq, h⟩
  · intro h
    apply (shuffleRound_order d types assign s s').mpr
    rcases h with h | ⟨heq, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨heq, h⟩
