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

/-- virtualPileTypes distributes over concatenation in the second argument. -/
theorem virtualPileTypes_append (pt1 A B : List PileType) :
    virtualPileTypes pt1 (A ++ B) = virtualPileTypes pt1 A ++ virtualPileTypes pt1 B := by
  simp [virtualPileTypes, List.flatMap_append]

/-- Replicating with all-Q outer types just repeats the inner list. -/
theorem virtualPileTypes_replicate_Q (pt : List PileType) (m : Nat) :
    virtualPileTypes pt (List.replicate m .Q) = (List.replicate m pt).flatten := by
  induction m with
  | zero => simp [virtualPileTypes]
  | succ m ih =>
    show applyPile .Q pt ++ virtualPileTypes pt (List.replicate m .Q) = _
    simp [applyPile, ih, List.replicate_succ, List.flatten_cons]

/-- virtualPileTypes distributes over flatten of replicated lists. -/
theorem virtualPileTypes_flatten_replicate (pt1 pt2 : List PileType) (m : Nat) :
    virtualPileTypes pt1 (List.replicate m pt2).flatten =
    (List.replicate m (virtualPileTypes pt1 pt2)).flatten := by
  induction m with
  | zero => simp [virtualPileTypes]
  | succ m ih =>
    simp only [List.replicate_succ, List.flatten_cons, virtualPileTypes_append, ih]

/-- Two-level virtualPileTypes with all-Q outer types equals single-level on flattened replicates. -/
theorem virtualPileTypes_replicate_Q_comp (pt1 pt2 : List PileType) (m : Nat) :
    virtualPileTypes (virtualPileTypes pt1 pt2) (List.replicate m .Q) =
    virtualPileTypes pt1 (List.replicate m pt2).flatten := by
  rw [virtualPileTypes_replicate_Q, virtualPileTypes_flatten_replicate]

theorem flatten_replicate_length {α : Type} (l : List α) (m : Nat) :
    (List.replicate m l).flatten.length = m * l.length := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.replicate_succ, List.flatten_cons, ih, Nat.succ_mul, Nat.add_comm]

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

theorem replicate_succ_append {α : Type} (m : Nat) (x : α) :
    List.replicate (m + 1) x = List.replicate m x ++ [x] := by
  induction m with
  | zero => rfl
  | succ m ih => exact congrArg (x :: ·) ih

/-- Peeling one Q from the front of a replicated virtualPileTypes. -/
theorem virtualPileTypes_replicate_Q_cons (inner : List PileType) (m : Nat) (hm : m ≥ 1) :
    virtualPileTypes inner (List.replicate m .Q) =
    inner ++ virtualPileTypes inner (List.replicate (m - 1) .Q) := by
  match m, hm with
  | m' + 1, _ =>
    rw [List.replicate_succ,
        show PileType.Q :: List.replicate m' PileType.Q =
             [PileType.Q] ++ List.replicate m' PileType.Q from rfl,
        virtualPileTypes_append]
    simp [virtualPileTypes, applyPile]

/-- Peeling one Q from the end of a replicated virtualPileTypes. -/
theorem virtualPileTypes_replicate_Q_snoc (inner : List PileType) (m : Nat) :
    virtualPileTypes inner (List.replicate (m + 1) .Q) =
    virtualPileTypes inner (List.replicate m .Q) ++ inner := by
  rw [replicate_succ_append, virtualPileTypes_append]
  simp [virtualPileTypes, List.flatMap_cons, List.flatMap_nil, applyPile]

/-- Length of replicated virtualPileTypes. -/
theorem virtualPileTypes_replicate_Q_length (inner : List PileType) (m : Nat) :
    (virtualPileTypes inner (List.replicate m .Q)).length = m * inner.length := by
  rw [virtualPileTypes_length, List.length_replicate]

/-- [Q] is a left identity for virtualPileTypes. -/
theorem virtualPileTypes_leftId (pt : List PileType) :
    virtualPileTypes [PileType.Q] pt = pt := by
  induction pt with
  | nil => simp [virtualPileTypes]
  | cons t rest ih =>
    show applyPile t [PileType.Q] ++ virtualPileTypes [PileType.Q] rest = t :: rest
    rw [ih]
    cases t <;> simp [applyPile, applyStack, invertType]

/-- Fold a list of pile-type rounds into a single equivalent round. -/
def foldVirtualPileTypes (rounds : List (List PileType)) : List PileType :=
  rounds.foldl virtualPileTypes [PileType.Q]

/-- Peeling one block from a two-level replicated virtualPileTypes:
    the outer Q-replication is converted to flat form with the first pt2-block
    separated from the remaining (m-1) repetitions. -/
theorem virtualPileTypes_replicate_peel (pt1 pt2 : List PileType) (m : Nat) (hm : m ≥ 1) :
    virtualPileTypes (virtualPileTypes pt1 pt2) (List.replicate m .Q) =
    virtualPileTypes pt1 (pt2 ++ (List.replicate (m - 1) pt2).flatten) := by
  rw [virtualPileTypes_replicate_Q_comp]
  congr 1
  match m, hm with
  | m' + 1, _ => simp [List.replicate_succ, List.flatten_cons]
