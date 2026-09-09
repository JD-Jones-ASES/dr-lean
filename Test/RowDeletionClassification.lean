import DR.Endpoint.RowDeletionClassification

namespace DittertRybin.Tests

private def threePairs : Fin 6 → Fin 3 := ![0,0,1,1,2,2]
private def tripleAndPair : Fin 5 → Fin 2 := ![0,0,0,1,1]

-- Three doubletons cannot be repaired by any two-row deletion.
private theorem threePairs_not_repairable :
    ∀ a b : Fin 6, ¬RowsDistinctOutside {a,b} threePairs := by
  unfold RowsDistinctOutside
  decide +kernel

example : rowDeletionMatrix threePairs=0 := by
  funext a b
  by_cases hab : a=b
  · subst b
    exact rowDeletionMatrix_self _ _
  · simp only [rowDeletionMatrix,if_neg hab,if_neg (threePairs_not_repairable a b),Matrix.zero_apply]

-- A tripleton and a doubleton also need at least three row deletions.
example : ∀ a b : Fin 5, ¬RowsDistinctOutside {a,b} tripleAndPair := by
  unfold RowsDistinctOutside
  decide +kernel

-- A repairable assignment can have two collision classes, not just one.
example : RowsDistinctOutside ({0,2} : Finset (Fin 4)) (![0,0,1,1] : Fin 4 → Fin 2) := by
  unfold RowsDistinctOutside
  decide +kernel

-- The generic classifier keeps every actual class; no positive weights or
-- dimensional lower bounds occur in its type.
example {m n : ℕ} (z : Fin m → Fin n) (a b : Fin m) (hab : a≠b)
    (h : RowsDistinctOutside {a,b} z) :
    Function.Injective z ∨
      (∃ V : Finset (Fin m), V.card=2 ∧ RowClassPattern V z) ∨
      (∃ V : Finset (Fin m), V.card=3 ∧ RowClassPattern V z) ∨
      ∃ V W : Finset (Fin m), V.card=2 ∧ W.card=2 ∧ Disjoint V W ∧ RowTwoClassPattern V W z :=
  classify_two_row_deletion z a b hab h

-- Empty rows and a single row have the zero deletion matrix, while the
-- classifier also correctly permits an injective assignment.
example (z : Fin 0 → Fin 0) : rowDeletionMatrix z=0 := by
  funext a
  exact Fin.elim0 a

example (z : Fin 1 → Fin 1) : rowDeletionMatrix z=0 := by
  funext a b
  have hab : a=b := Subsingleton.elim _ _
  subst b
  exact rowDeletionMatrix_self _ _

-- The fiber bound includes classes containing neither deleted row.
example {m n : ℕ} (z : Fin m → Fin n) (S : Finset (Fin m))
    (h : RowsDistinctOutside S z) (u : Fin n) :
    (rowColumnFiber z u \ S).card≤1 := rowColumnFiber_outside_card_le_one S h u

#print axioms rowColumnFiber_outside_card_le_one
#print axioms two_row_fibers_pattern
#print axioms RowTwoClassPattern.drop_singleton_right
#print axioms classify_two_row_deletion
#print axioms rowDeletionMatrix_zero_or_pattern

end DittertRybin.Tests
