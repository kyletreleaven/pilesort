/-
  Virtual pile type composition for multi-round pile shuffle.

  Mirrors multiround.py:
    virtual_pile_types(pt1, pt2) composes two rounds of pile types
    into equivalent single-round virtual pile types.

  Q acts as identity on the pile type sequence.
  S reverses and inverts all types (Q↔S).
-/
import PileSort.Basic

def invertType : PileType → PileType
  | .Q => .S
  | .S => .Q

def applyStack (pileTypes : List PileType) : List PileType :=
  (pileTypes.reverse).map invertType

def applyPile (pileType : PileType) (pileTypes : List PileType) : List PileType :=
  match pileType with
  | .Q => pileTypes
  | .S => applyStack pileTypes

def virtualPileTypes (pt1 pt2 : List PileType) : List PileType :=
  pt2.flatMap (fun typ => applyPile typ pt1)

theorem applyPile_length (t : PileType) (pt : List PileType) :
    (applyPile t pt).length = pt.length := by
  cases t <;> simp [applyPile, applyStack]

/-- (A ++ B)[A.length + i] = B[i] -/
theorem getElem_append_add {α : Type} (A B : List α) (i : Nat)
    (hi : i < B.length) (hb : A.length + i < (A ++ B).length) :
    (A ++ B)[A.length + i] = B[i] := by
  rw [List.getElem_append_right (by omega : A.length ≤ A.length + i)]
  congr 1; omega

/-- k*m + j < n*m when k < n and j < m -/
theorem block_index_bound {k j n m : Nat} (hk : k < n) (hj : j < m) :
    k * m + j < n * m := by
  calc k * m + j
    _ < k * m + m := by omega
    _ = (k + 1) * m := by rw [Nat.succ_mul]
    _ ≤ n * m := Nat.mul_le_mul_right _ (by omega)

theorem virtualPileTypes_length (pt1 pt2 : List PileType) :
    (virtualPileTypes pt1 pt2).length = pt2.length * pt1.length := by
  induction pt2 with
  | nil => simp [virtualPileTypes]
  | cons x rest ih =>
    show (applyPile x pt1 ++ virtualPileTypes pt1 rest).length = _
    rw [List.length_append, applyPile_length, ih,
        List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Position k*m+j in virtualPileTypes maps to position j in the k-th block. -/
theorem virtualPileTypes_getElem (pt1 pt2 : List PileType) (k j : Nat)
    (hk : k < pt2.length) (hj : j < pt1.length)
    (hb : k * pt1.length + j < (virtualPileTypes pt1 pt2).length :=
      by rw [virtualPileTypes_length]; exact block_index_bound hk hj) :
    (virtualPileTypes pt1 pt2)[k * pt1.length + j] =
    (applyPile pt2[k] pt1)[j]'(by rw [applyPile_length]; exact hj) := by
  induction pt2 generalizing k with
  | nil => simp at hk
  | cons x rest ih =>
    cases k with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      exact List.getElem_append_left ..
    | succ k' =>
      have hk' : k' < rest.length := by
        have := List.length_cons x rest; omega
      show (applyPile x pt1 ++ virtualPileTypes pt1 rest)[(k' + 1) * pt1.length + j] = _
      have hidx : (k' + 1) * pt1.length + j =
          (applyPile x pt1).length + (k' * pt1.length + j) := by
        rw [applyPile_length, Nat.succ_mul]; omega
      simp only [hidx, getElem_append_add _ _ _ (by rw [virtualPileTypes_length]
                                                    exact block_index_bound hk' hj)]
      exact ih k' hk' (by rw [virtualPileTypes_length]; exact block_index_bound hk' hj)
