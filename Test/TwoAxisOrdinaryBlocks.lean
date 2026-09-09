import DR.Certificates.TwoAxisOrdinaryBlocks

namespace DittertRybin.Tests
open Certificates
noncomputable section

example : ordinaryPair (.inr 3 : Fin 2 ⊕ ℕ) (.inr 4) = .different := by decide
example : ordinaryPair (.inr 3 : Fin 2 ⊕ ℕ) (.inr 3) = .same := by decide
example : ordinaryPair (.inl 0 : Fin 2 ⊕ ℕ) (.inr 3) = .toOrdinary 0 := rfl

-- Multiplicity one discards the unequal-ordinary entry, whatever its sign.
example : ordinaryPairAverage 1 (α := Fin 0)
    (fun p => match p with | .same => 1 | _ => -100) (.inr ()) (.inr ()) = 1 := by
  simp

-- The aggregate is a sum coordinate and carries the product of the two counts.
example : twoAxisAggregateWeight (α := Fin 1) (β := Fin 1) 2 3
    (.inr (),.inr ()) = 6 := by norm_num [twoAxisAggregateWeight,ordinaryAxisWeight]

private def singletonSectorKernel : OrdinaryPair (Fin 0) → OrdinaryPair (Fin 0) → ℝ
  | .same, .same => 1
  | .different, .same => 2
  | .same, .different => 2
  | _, _ => 0

-- The absent interaction sector can be negative at R=C=1.
example : twoAxisInteraction singletonSectorKernel = -3 := by
  norm_num [twoAxisInteraction,singletonSectorKernel]

example : quadraticValue (twoAxisOrdinaryMatrix (ρ := Unit) (γ := Unit)
    singletonSectorKernel) (fun _ => 1) = 1 := by
  simp [quadraticValue,twoAxisOrdinaryMatrix,ordinaryPair,singletonSectorKernel,
    Fintype.sum_prod_type,Fintype.sum_sum_type]

#print axioms twoAxisOrdinaryMatrix_isSymm
#print axioms twoAxisTrivialMatrix_averages_commute
#print axioms ordinaryPairMatrix_reindex
#print axioms ordinaryPairAggregate_reindex
#print axioms quadraticValue_ordinaryPair_decomposition

end
end DittertRybin.Tests
