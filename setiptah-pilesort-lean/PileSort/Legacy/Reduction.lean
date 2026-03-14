import PileSort.Reduction

/-- Tail-recursive computation of the formulaWord endpoint, specialized for
    the clause-by-clause structure. At each level, the types have
    `clauses_.length + 2` Q-replications (remaining + last + vestigial).
    The recursive case peels off one clause, accumulating one block's worth
    of offset via the shift property of `compile_append_right`. -/
def formulaState (n : Nat) (xs : List PileType)
    (clauses_ : List Clause) (last : Clause) (start : Nat) : Nat :=
  let types := virtualPileTypes (virtualPileTypes ALIGN xs)
      (List.replicate (clauses_.length + 2) .Q)
  let block := xs.length * ALIGN.length
  match clauses_ with
  | [] => applyWord (clauseWord n last) (compile types) start
  | c :: rest =>
    block + formulaState n xs rest last
      (applyWord (clauseWord n c ++ NEXT) (compile types) start - block)
