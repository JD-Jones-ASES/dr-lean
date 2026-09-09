import DR.Rectangular.FourRowMinorantThreeStationary
import DR.Rectangular.FourRowMinorantThreeBoundary

namespace DittertRybin.Test.FourRowMinorantThreeStationary
open scoped BigOperators

example : fourRowThreeStationary 1 1 1 1 = ![1/3,1/3,1/3,0] := by
  funext i
  fin_cases i <;> norm_num [fourRowThreeStationary,fourRowThreePhi,
    fourRowThreeDenominator,Matrix.cons_val_two,Matrix.cons_val_three]

example : fourRowMinorantHomogeneous ![1,1,1,1] (fourRowThreeStationary 1 1 1 1)=2/3 := by
  rw [fourRowThreeStationary_value _ _ _ _ (by norm_num [fourRowThreeDenominator])]
  norm_num [fourRowThreeValueBase,fourRowThreeValueSlope,fourRowThreeDenominator]

-- The nonzero denominator is necessary for the mass identity.
example : (∑ i, fourRowThreeStationary 4 1 1 1 i)=0 := by
  norm_num [fourRowThreeStationary,fourRowThreeDenominator,Fin.sum_univ_succ,
    Matrix.cons_val_two,Matrix.cons_val_three]

-- D>0 alone does not make the unconstrained stationary vector feasible.
example :
    0 < fourRowThreeDenominator 5 7 10 ∧
    fourRowThreeStationary 3 1 1 10 0 = -1/30 := by
  norm_num [fourRowThreeStationary,fourRowThreePhi,fourRowThreeDenominator]

-- Both alternative repeated-pair orientations use the actual face theorem.
example (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i = 1) (h3 : v 3=0) :
    0 ≤ fourRowMinorantHomogeneous ![2,2,3,1] v := by
  apply fourRowMinorantHomogeneous_repeated_active_nonneg _ v _ hv hvs h3 (Or.inl rfl)
  intro i; fin_cases i <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three]

example (v : Fin 4 → ℝ) (hv : ∀ i, 0 ≤ v i) (hvs : ∑ i, v i = 1) (h3 : v 3=0) :
    0 ≤ fourRowMinorantHomogeneous ![2,3,2,1] v := by
  apply fourRowMinorantHomogeneous_repeated_active_nonneg _ v _ hv hvs h3 (Or.inr (Or.inl rfl))
  intro i; fin_cases i <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three]

#print axioms fourRowThreePhi_mass
#print axioms fourRowThreeStationary_sum
#print axioms fourRowThreeStationary_gradient
#print axioms fourRowThreeStationary_value
#print axioms fourRowMinorantHomogeneous_pair_nonneg_of_pos_mass
#print axioms fourRowMinorantHomogeneous_repeated_active_nonneg

end DittertRybin.Test.FourRowMinorantThreeStationary
