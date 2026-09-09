import DR.Rectangular.FourRowMinorantInterior

/-!
# Feasible one-large-row stationary vectors

The nonnegative distinguished stationary coordinate forces R < 7/16.
The exact stationary value is then strictly positive for 1/4 < R < 1/2.
The feasibility premise is essential and is retained explicitly.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowMinorantOneLargeRows (R : ℝ) : Fin 4 → ℝ :=
  ![R, (1-R)/3, (1-R)/3, (1-R)/3]

theorem fourRowMinorantOneLargeRows_sum (R : ℝ) :
    ∑ i, fourRowMinorantOneLargeRows R i = 1 := by
  simp [fourRowMinorantOneLargeRows, Fin.sum_univ_four,
    Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem fourRowMinorantOneLargeRows_delta (R : ℝ) :
    fourRowMinorantDelta (fourRowMinorantOneLargeRows R) = 2*R*(1-2*R) := by
  norm_num [fourRowMinorantDelta, fourRowMinorantSquareSum, fourRowMinorantOneLargeRows,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

theorem fourRowMinorantOneLarge_big (R : ℝ) (hR : R ≠ 0) (hh : 1-2*R ≠ 0) :
    fourRowMinorantStationary (fourRowMinorantOneLargeRows R) 0 =
      (4*R^2-11*R+4)/(12*(1-2*R)) := by
  rw [fourRowMinorantStationary, fourRowMinorantOneLargeRows_delta]
  norm_num [fourRowMinorantSquareSum, fourRowMinorantOneLargeRows,
    Fin.sum_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  have hh' : 1-R*2 ≠ 0 := by simpa only [mul_comm] using hh
  field_simp [hR, hh, hh']
  ring

theorem fourRowMinorantOneLarge_value (R : ℝ) (hR : R ≠ 0) (hh : 1-2*R ≠ 0) :
    fourRowMinorantStationaryValue (fourRowMinorantOneLargeRows R) =
      -(R-1)*(4*R-1)^2*(R^2+16*R-8)/(324*(2*R-1)) := by
  unfold fourRowMinorantStationaryValue
  rw [fourRowMinorantOneLargeRows_delta, fourRowMinorantE3_expand]
  norm_num [fourRowMinorantSquareSum, fourRowMinorantOneLargeRows,
    Fin.sum_univ_four, Fin.prod_univ_four, Matrix.cons_val_two, Matrix.cons_val_three]
  have hh' : 1-R*2 ≠ 0 := by simpa only [mul_comm] using hh
  have hh'' : -1+R*2 ≠ 0 := by intro h; apply hh; linarith
  field_simp [hR, hh, hh', hh'']
  ring_nf
  field_simp [hh'']
  ring

/-- Feasibility of the largest stationary coordinate forces the stronger rational cutoff. -/
theorem fourRowMinorantOneLarge_feasible_cutoff (R : ℝ) (hR : 1/4 < R) (hh : R < 1/2)
    (hv : 0 ≤ fourRowMinorantStationary (fourRowMinorantOneLargeRows R) 0) : R < 7/16 := by
  have hp : 0 < 1-2*R := by linarith
  rw [fourRowMinorantOneLarge_big R (by linarith) hp.ne'] at hv
  have hnum := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<12) hp)).mp hv
  simp only [zero_mul] at hnum
  by_contra h
  have hlow : 7/16 ≤ R := le_of_not_gt h
  nlinarith [mul_nonneg (sub_nonneg.mpr hlow) (sub_nonneg.mpr hh.le)]

/-- The actual stationary value is strictly positive on the feasible nonuniform one-large family. -/
theorem fourRowMinorantOneLarge_value_pos (R : ℝ) (hR : 1/4 < R) (hh : R < 1/2)
    (hv : 0 ≤ fourRowMinorantStationary (fourRowMinorantOneLargeRows R) 0) :
    0 < fourRowMinorantHomogeneous (fourRowMinorantOneLargeRows R)
      (fourRowMinorantStationary (fourRowMinorantOneLargeRows R)) := by
  have hp : 0 < 1-2*R := by linarith
  have hd : fourRowMinorantDelta (fourRowMinorantOneLargeRows R) ≠ 0 := by
    rw [fourRowMinorantOneLargeRows_delta]
    positivity
  rw [fourRowMinorantStationary_value _ (fourRowMinorantOneLargeRows_sum R) hd,
    fourRowMinorantOneLarge_value R (by linarith) hp.ne']
  have hcut := fourRowMinorantOneLarge_feasible_cutoff R hR hh hv
  have hpoly : R^2+16*R-8 < 0 := by
    have hmul := mul_nonneg (show 0 ≤ 7/16-R by linarith) (show 0 ≤ 7/16+R by linarith)
    nlinarith
  have hsquare : 0 < (4*R-1)^2 := sq_pos_of_pos (by linarith)
  apply div_pos_of_neg_of_neg
  · exact mul_neg_of_pos_of_neg (mul_pos (by linarith) hsquare) hpoly
  · linarith

end DittertRybin
