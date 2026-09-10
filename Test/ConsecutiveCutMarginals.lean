import DR.Endpoint.ConsecutiveCutShared

namespace DittertRybin.Tests
open scoped BigOperators

-- Both sides of one use the scalar logarithmic proof, with the same closed cap.
example : ((101/100 : ℝ)-1)^2/(2*(101/100 : ℝ)^2) ≤
    (101/100 : ℝ)-1-Real.log (101/100) :=
  log_deficit_ge_sq_of_upper_cap (by norm_num) (by norm_num) le_rfl
example : ((1/2 : ℝ)-1)^2/(2*(101/100 : ℝ)^2) ≤
    (1/2 : ℝ)-1-Real.log (1/2) :=
  log_deficit_ge_sq_of_upper_cap (by norm_num) (by norm_num) (by norm_num)
example : ((1 : ℝ)-1)^2/(2*(1 : ℝ)^2) ≤ 1-1-Real.log 1 :=
  log_deficit_ge_sq_of_upper_cap (by norm_num) le_rfl le_rfl

-- Projection remains valid for signed total-one data, not only positive rows.
example : ((∑ i ∈ ({0} : Finset (Fin 2)), (![2,-1] : Fin 2 → ℝ) i)-1/2)^2 ≤
    (1/2 : ℝ)*marginalVariance (![2,-1] : Fin 2 → ℝ) := by
  convert probability_subset_sq_le_card_variance (by decide : 0 < 2)
    (![2,-1] : Fin 2 → ℝ) (by norm_num [Fin.sum_univ_succ]) {0} using 1 <;> norm_num

example {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) (hs : ∑ i, x i = 1) :
    ((∑ i ∈ (∅ : Finset (Fin d)), x i)-(∅ : Finset (Fin d)).card/(d : ℝ))^2 ≤
      ((∅ : Finset (Fin d)).card : ℝ)*((d : ℝ)-(∅ : Finset (Fin d)).card)/(d : ℝ)*marginalVariance x :=
  probability_subset_sq_le_card_variance hd x hs ∅
example {d : ℕ} (hd : 0 < d) (x : Fin d → ℝ) (hs : ∑ i, x i = 1) :
    ((∑ i, x i)-(d : ℝ)/(d : ℝ))^2 ≤ 0*marginalVariance x := by
  simpa using probability_subset_sq_le_card_variance hd x hs Finset.univ

example : endpointSizedRowCutCoefficient (101/100) 19 0 = 0 ∧
    endpointSizedRowCutCoefficient (101/100) 19 19 = 0 := by
  norm_num [endpointSizedRowCutCoefficient]
example : endpointSizedColumnCutCoefficient 19 20 0 = 0 ∧
    endpointSizedColumnCutCoefficient 19 20 20 = 0 := by
  norm_num [endpointSizedColumnCutCoefficient]

-- The actual first finite board dimension obtains H=101/100 without a cap assumption.
example (P : Board 19 20) (hP : IsProbability P)
    (hcont : uniformSeparationValue 19 20 19 ≤ separationProbability P 19)
    (I : Finset (Fin 19)) (J : Finset (Fin 20)) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(19 : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/(20 : ℝ)|)^2 ≤
      (endpointSizedRowCutCoefficient (101/100) 19 I.card +
        (dittertConstant 19/distinctUniformProbability 20 19)*endpointSizedColumnCutCoefficient 19 20 J.card)*
        endpointRookDeficit P/(1-distinctUniformProbability 20 19) := by
  apply endpoint_contender_sized_subset_discrepancy_sq (by decide) (by decide) hP hcont (by norm_num)
  norm_num [distinctUniformProbability, Nat.descFactorial]

-- The incorrect replacement of k(d-k)/d by its square would fail already for a singleton.
example : ¬((2 : ℝ)-1/2)^2 ≤ (1/2 : ℝ)^2*marginalVariance (![2,-1] : Fin 2 → ℝ) := by
  norm_num [marginalVariance, Fin.sum_univ_succ]

#print axioms log_deficit_ge_sq_of_upper_cap
#print axioms capped_product_square_sum_le
#print axioms probability_subset_sq_le_card_variance
#print axioms probability_product_variance_le_of_cap
#print axioms endpoint_contender_row_variance_of_cap
#print axioms endpoint_contender_sized_row_subset_sq
#print axioms endpoint_contender_column_variance
#print axioms endpoint_contender_sized_column_subset_sq
#print axioms endpoint_contender_sized_subset_discrepancy_sq
#print axioms endpoint_contender_sized_cut_discrepancy_sq

end DittertRybin.Tests
