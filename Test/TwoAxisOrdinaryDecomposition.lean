import DR.Certificates.TwoAxisOrdinaryDecomposition

namespace DittertRybin.Tests
open Certificates
noncomputable section

private theorem fin3_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem fin3_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
private theorem fin3_one_ne_two : (1 : Fin 3) ≠ 2 := by decide
private theorem fin3_two_ne_one : (2 : Fin 3) ≠ 1 := by decide

private def contrastKernel : OrdinaryPair (Fin 0) → OrdinaryPair (Fin 0) → ℝ
  | .same,.same => 1
  | .different,.same => 2
  | .same,.different => 3
  | .different,.different => 7
  | _,_ => 0

example : TwoAxisOrdinarySymm contrastKernel := by
  intro r c
  cases r <;> cases c <;> rfl

-- Exact average denominators and all four signs are visible on a2×3 ordinary block.
example : twoAxisTrivialMatrix contrastKernel 2 3 (.inr (),.inr ()) (.inr (),.inr ()) = 23/6 := by
  norm_num [twoAxisTrivialMatrix,ordinaryPairAverage,contrastKernel]

example : twoAxisRowStandardMatrix contrastKernel 3 (.inr ()) (.inr ()) = -3 := by
  norm_num [twoAxisRowStandardMatrix,ordinaryPairAverage,contrastKernel]

example : twoAxisColumnStandardMatrix contrastKernel 2 (.inr ()) (.inr ()) = -7/2 := by
  norm_num [twoAxisColumnStandardMatrix,ordinaryPairAverage,contrastKernel]

example : twoAxisInteraction contrastKernel = 3 := by
  norm_num [twoAxisInteraction,contrastKernel]

-- Pure row contrast has negative quadratic value; no implicit PSD was assumed.
example : quadraticValue (twoAxisOrdinaryMatrix (ρ := Fin 2) (γ := Fin 3) contrastKernel)
    (fun p => if p.1 = .inr 0 then 1 else -1) = -54 := by
  norm_num [quadraticValue,twoAxisOrdinaryMatrix,ordinaryPair,contrastKernel,
    Fintype.sum_prod_type,Fintype.sum_sum_type,Fin.sum_univ_succ,
    fin3_zero_ne_two,fin3_two_ne_zero,fin3_one_ne_two,fin3_two_ne_one]

-- Pure column contrast is scaled by the row aggregate, retaining1/R.
example : quadraticValue (twoAxisOrdinaryMatrix (ρ := Fin 2) (γ := Fin 3) contrastKernel)
    (fun p => if p.2 = .inr 0 then 1 else if p.2 = .inr 1 then -1 else 0) = -28 := by
  norm_num [quadraticValue,twoAxisOrdinaryMatrix,ordinaryPair,contrastKernel,
    Fintype.sum_prod_type,Fintype.sum_sum_type,Fin.sum_univ_succ,
    fin3_zero_ne_two,fin3_two_ne_zero,fin3_one_ne_two,fin3_two_ne_one]

-- The doubly centered contrast is governed by the full alternating interaction.
example : quadraticValue (twoAxisOrdinaryMatrix (ρ := Fin 2) (γ := Fin 3) contrastKernel)
    (fun p => (if p.1 = .inr 0 then 1 else -1) *
      (if p.2 = .inr 0 then 1 else if p.2 = .inr 1 then -1 else 0)) = 12 := by
  norm_num [quadraticValue,twoAxisOrdinaryMatrix,ordinaryPair,contrastKernel,
    Fintype.sum_prod_type,Fintype.sum_sum_type,Fin.sum_univ_succ,
    fin3_zero_ne_two,fin3_two_ne_zero,fin3_one_ne_two,fin3_two_ne_one]

#print axioms quadraticValue_ordinaryScalar_decomposition
#print axioms quadraticValue_ordinaryColumnPair_decomposition
#print axioms quadraticValue_twoAxis_decomposition
#print axioms twoAxisAggregateVector_constant

end
end DittertRybin.Tests
