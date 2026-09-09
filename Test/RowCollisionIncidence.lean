import DR.Endpoint.RowCollisionIncidence

namespace DittertRybin.Tests
open scoped BigOperators

private def pair : Fin 3 → Fin 2 := ![0,0,1]
private def triple : Fin 3 → Fin 1 := fun _ => 0
private def twoPairs : Fin 4 → Fin 2 := ![0,0,1,1]
private theorem hp : RowClassPattern ({0,1} : Finset (Fin 3)) pair := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel
private theorem ht : RowClassPattern (Finset.univ : Finset (Fin 3)) triple := by
  unfold RowClassPattern RowClassEvent RowCollisionEvent
  decide +kernel
private theorem htw : RowTwoClassPattern ({0,1} : Finset (Fin 4)) {2,3} twoPairs := by
  unfold RowTwoClassPattern RowClassEvent RowCollisionEvent
  decide +kernel

example : rowDoubletonIncidence pair 0=1 := by
  rw [rowDoubletonIncidence_of_pair hp (by decide)]
  norm_num [rowClassIncidence]

example : rowDoubletonIncidence pair 2=0 := by
  rw [rowDoubletonIncidence_of_pair hp (by decide)]
  norm_num [rowClassIncidence,Fin.ext_iff,-Fin.val_eq_zero_iff]

example : rowDeficitTwoIncidence pair 0=0 := by
  have hn := rowDoubleton_not_deficitTwo (show HasRowDoubletonPattern pair from ⟨_,by decide,hp⟩)
  simp [rowDeficitTwoIncidence,hn]

-- A row in a tripleton participates once, despite its two collision edges.
example : rowDeficitTwoIncidence triple 0=1 := by
  rw [rowDeficitTwoIncidence_of_triple ht (by decide)]
  simp [rowClassIncidence]
example : (∑ i,rowDeficitTwoIncidence triple i)=3 := by
  simp_rw [rowDeficitTwoIncidence_of_triple ht (by decide)]
  simp [rowClassIncidence]

-- Two doubletons contribute one per participating row, irrespective of
-- which of their two class labels is listed first.
example : (∑ i,rowDeficitTwoIncidence twoPairs i)=4 := by
  simp_rw [rowDeficitTwoIncidence_of_two_pairs htw (by decide) (by decide) (by decide)]
  rw [sum_rowClassIncidence]
  have hc : (({0,1} : Finset (Fin 4))∪{2,3}).card=4 := by decide
  exact_mod_cast hc

example : ¬HasRowDoubletonPattern triple := by
  intro h
  exact rowDoubleton_not_deficitTwo h (Or.inl ⟨_,by decide,ht⟩)

example (i : Fin 3) : rowDoubletonIncidence (fun j : Fin 3 => j) i=0 := by
  simp [rowDoubletonIncidence,rowCollisionParticipant_not_injective (fun _ _ h => h) i]

#print axioms RowClassPattern.class_subset
#print axioms RowClassPattern.unique_class
#print axioms RowClassPattern.participant_iff
#print axioms RowTwoClassPattern.participant_iff
#print axioms rowDoubleton_not_deficitTwo
#print axioms rowDeletion_pointwise_lower

end DittertRybin.Tests
