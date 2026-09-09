import DR.Rectangular.FourRowMinorantOneLarge

open DittertRybin
open scoped BigOperators

-- The exact stationary vector retains total mass even at the excluded singular denominator.
example : (∑ i, fourRowMinorantStationary ![0,1/3,1/3,1/3] i) = 1 :=
  fourRowMinorantStationary_sum _ (by
    norm_num [Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three])

example : fourRowMinorantDelta ![0,1/3,1/3,1/3] = 0 := by
  norm_num [fourRowMinorantDelta, fourRowMinorantSquareSum,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]

example (r : Fin 4 → ℝ) (hs : ∑ i,r i=1) (hd : fourRowMinorantDelta r ≠ 0)
    (i j : Fin 4) :
    fourRowMinorantGradient r (fourRowMinorantStationary r) i =
      fourRowMinorantGradient r (fourRowMinorantStationary r) j := by
  rw [fourRowMinorantStationary_gradient r hs hd, fourRowMinorantStationary_gradient r hs hd]

-- The infeasible negative stationary value is not a minorant counterexample.
example : fourRowMinorantStationary (fourRowMinorantOneLargeRows (49/100)) 0 = -179/100 := by
  rw [fourRowMinorantOneLarge_big _ (by norm_num) (by norm_num)]
  norm_num

example : fourRowMinorantStationaryValue (fourRowMinorantOneLargeRows (49/100)) = -4539/781250 := by
  rw [fourRowMinorantOneLarge_value _ (by norm_num) (by norm_num)]
  norm_num

example : ¬ (∀ i, 0 ≤ fourRowMinorantStationary (fourRowMinorantOneLargeRows (49/100)) i) := by
  intro h
  have h0 := h 0
  rw [fourRowMinorantOneLarge_big _ (by norm_num) (by norm_num)] at h0
  norm_num at h0

example : fourRowMinorantStationaryValue (fourRowMinorantOneLargeRows (1/4)) = 0 := by
  rw [fourRowMinorantOneLarge_value _ (by norm_num) (by norm_num)]
  norm_num

-- Feasibility at the distinguished coordinate is enough for the exact strict conclusion.
example (R : ℝ) (hR : 1/4 < R) (hh : R < 1/2)
    (hv : 0 ≤ fourRowMinorantStationary (fourRowMinorantOneLargeRows R) 0) :
    0 < fourRowMinorantHomogeneous (fourRowMinorantOneLargeRows R)
      (fourRowMinorantStationary (fourRowMinorantOneLargeRows R)) :=
  fourRowMinorantOneLarge_value_pos R hR hh hv

example : 0 < fourRowMinorantHomogeneous (fourRowMinorantOneLargeRows (2/5))
    (fourRowMinorantStationary (fourRowMinorantOneLargeRows (2/5))) := by
  apply fourRowMinorantOneLarge_value_pos _ (by norm_num) (by norm_num)
  rw [fourRowMinorantOneLarge_big _ (by norm_num) (by norm_num)]
  norm_num

#print axioms fourRowMinorantStationary_sum
#print axioms fourRowMinorantStationary_gradient
#print axioms fourRowMinorantStationary_value
#print axioms fourRowMinorantOneLarge_feasible_cutoff
#print axioms fourRowMinorantOneLarge_value_pos
