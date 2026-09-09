import DR.Rectangular.FourRowMinorantFinal

namespace DittertRybin.Test.FourRowMinorantFinal
open scoped BigOperators

-- Exact principal type: neither support positivity nor a stationary-vector premise.
example (r v : Fin 4 → ℝ) (hr : ∀ i,0≤r i) (hsr : ∑ i,r i=1)
    (hv : ∀ i,0≤v i) (hsv : ∑ i,v i=1) :
    (∑ i,v i*(1-fourRowGaugeCollision r i)) ≤
      Certificates.quadraticValue (fourRowLeadingKernel r) v :=
  fourRow_corrected_minorant r v hr hsr hv hsv

-- Interior row vector with an infeasible unconstrained stationary vector;
-- the principal theorem still covers every actual probability v.
example (v : Fin 4 → ℝ) (hv : ∀ i,0≤v i) (hsv : ∑ i,v i=1) :
    0 ≤ fourRowMinorantHomogeneous ![49/100,17/100,17/100,17/100] v := by
  apply fourRowMinorantHomogeneous_nonneg _ v _ _ hv hsv
  · intro i
    fin_cases i <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three]
  · norm_num [Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]

-- Simultaneous multiple zero rows and a full-support v distribution.
example (v : Fin 4 → ℝ) (hv : ∀ i,0≤v i) (hsv : ∑ i,v i=1) :
    0 ≤ fourRowMinorantHomogeneous ![1,0,0,0] v := by
  apply fourRowMinorantHomogeneous_nonneg _ v _ _ hv hsv
  · intro i
    fin_cases i <;> norm_num [Matrix.cons_val_two,Matrix.cons_val_three]
  · norm_num [Fin.sum_univ_succ]

#print axioms fourRowMinorantFixedFeasible_isCompact
#print axioms exists_fourRowMinorant_fixed_maximum
#print axioms fourRowMinorantStationary_feasible_nonneg
#print axioms fourRowMinorantHomogeneous_nonneg
#print axioms fourRow_corrected_minorant

end DittertRybin.Test.FourRowMinorantFinal
