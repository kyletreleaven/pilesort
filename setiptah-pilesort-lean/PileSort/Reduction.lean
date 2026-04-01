/-
  SAT-to-pile-sort reduction: data types and embedding functions.
-/
import PileSort.Basic
import PileSort.MatchingChain
import PileSort.SAT
import PileSort.VirtualPileTypes
import PileSort.Words

/-- The test word for variable i in clause φ_j:
    POS if x_i ∈ φ_j, NEG if ¬x_i ∈ φ_j, DK otherwise. -/
def testWord (i : Nat) (clause : Clause) : List Action :=
  match clause.getD i .absent with
  | .pos => POS
  | .neg => NEG
  | .absent => DK

/-- The end-test word for variable i in clause φ_j:
    ENDPOS if x_i ∈ φ_j, ENDNEG if ¬x_i ∈ φ_j, ENDDK otherwise. -/
def endTestWord (i : Nat) (clause : Clause) : List Action :=
  match clause.getD i .absent with
  | .pos => ENDPOS
  | .neg => ENDNEG
  | .absent => ENDDK

/-- Word embedding of a clause over n variables:
    START_CLAUSE ++ test_0(φ) ++ ... ++ test_{n-2}(φ) ++ endtest_{n-1}(φ) -/
def clauseWord (n : Nat) (clause : Clause) : List Action :=
  START_CLAUSE ++
  (List.range (n - 1)).flatMap (fun i => testWord i clause) ++
  endTestWord (n - 1) clause

/-- Word embedding of a formula (list of clauses) over n variables:
    clause(φ_0) ++ NEXT ++ clause(φ_1) ++ NEXT ++ ... ++ clause(φ_{m-1}) -/
def formulaWord (n : Nat) (clauses : List Clause) : List Action :=
  (clauses.flatMap (fun c => clauseWord n c ++ NEXT)).dropLast

theorem formulaWord_split (n : Nat) (init : List Clause) (last : Clause) :
    formulaWord n (init ++ [last]) =
    (init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last := by
  unfold formulaWord
  rw [List.flatMap_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [← List.append_assoc]
  show ((init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last ++ NEXT).dropLast =
    (init.flatMap (fun c => clauseWord n c ++ NEXT)) ++ clauseWord n last
  unfold NEXT
  rw [List.dropLast_concat]

/-- Peeling the first clause off a formulaWord. -/
theorem formulaWord_cons (n : Nat) (c : Clause) (rest : List Clause) (last : Clause) :
    formulaWord n ((c :: rest) ++ [last]) =
    (clauseWord n c ++ NEXT) ++ formulaWord n (rest ++ [last]) := by
  rw [formulaWord_split, formulaWord_split]
  simp [List.flatMap_cons, List.append_assoc]
