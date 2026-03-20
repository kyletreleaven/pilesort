/-
  Ordering lemmas for elements in a nodup concatenation of lists.

  Given a list of lists whose flatten is Nodup:
  1. If a ∈ lists[i] and b ∈ lists[j] with i < j, then a precedes b in the flatten.
  2. If a, b ∈ lists[i], their order in the flatten equals their order within lists[i].
-/
import PileSort.Permutations

/-- In a Nodup flatten, indexOf a (where a ∈ lists[i]) equals the flattened prefix
    length plus indexOf a within lists[i] alone. -/
private theorem indexOf_flatten_eq {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) (i : Fin lists.length) {a : α} (ha : a ∈ lists.get i) :
    lists.flatten.indexOf a = (lists.take i.val).flatten.length + (lists.get i).indexOf a := by
  sorry

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
  rw [indexOf_flatten_eq lists hnd i ha, indexOf_flatten_eq lists hnd i hb]
  omega

/-- Nat-index corollary of `indexOf_flatten_of_lt`. -/
theorem indexOf_flatten_of_lt_val {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i j : Nat} (hi : i < lists.length) (hj : j < lists.length)
    (hij : i < j) {a b : α} (ha : a ∈ lists[i]'hi) (hb : b ∈ lists[j]'hj) :
    lists.flatten.indexOf a < lists.flatten.indexOf b :=
  indexOf_flatten_of_lt lists hnd hij ha hb

/-- Nat-index corollary of `indexOf_flatten_same`. -/
theorem indexOf_flatten_same_val {α : Type} [DecidableEq α] (lists : List (List α))
    (hnd : lists.flatten.Nodup) {i : Nat} (hi : i < lists.length)
    {a b : α} (ha : a ∈ lists[i]'hi) (hb : b ∈ lists[i]'hi) :
    lists.flatten.indexOf a < lists.flatten.indexOf b ↔
    (lists[i]'hi).indexOf a < (lists[i]'hi).indexOf b :=
  indexOf_flatten_same lists hnd ha hb
