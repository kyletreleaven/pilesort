/-
  Ordering lemmas for elements in a nodup concatenation of lists.

  Given a list of lists whose flatten is Nodup:
  1. If a ∈ lists[i] and b ∈ lists[j] with i < j, then a precedes b in the flatten.
  2. If a, b ∈ lists[i], their order in the flatten equals their order within lists[i].
-/

/-- If the flatten of a list of lists is Nodup, and a ∈ lists[i], b ∈ lists[j] with i < j,
    then a precedes b in the flatten. -/
theorem indexOf_flatten_of_lt {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i j : Fin lists.length} (hij : i < j)
    {a b : α} (ha : a ∈ lists.get i) (hb : b ∈ lists.get j) :
    lists.flatten.indexOf a < lists.flatten.indexOf b := by
  sorry

/-- If the flatten of a list of lists is Nodup, and a, b ∈ lists[i],
    their order in the flatten equals their order within lists[i]. -/
theorem indexOf_flatten_same {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i : Fin lists.length}
    {a b : α} (ha : a ∈ lists.get i) (hb : b ∈ lists.get i) :
    lists.flatten.indexOf a < lists.flatten.indexOf b ↔
    (lists.get i).indexOf a < (lists.get i).indexOf b := by
  sorry
