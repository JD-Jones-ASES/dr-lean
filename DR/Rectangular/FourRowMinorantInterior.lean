import DR.Rectangular.FourRowMinorantDefinitions
import DR.Rectangular.FourRowScalarGaugePolynomial

/-!
# Exact interior stationary algebra for the corrected four-row minorant

The stationary vector is defined without a feasibility assertion. Its exact
value may be negative when a coordinate is negative; the later minimization
argument must retain feasibility. The gradient and value identities retain
a nonzero `1 - 3 q` hypothesis; total mass also holds at its zero value.
-/

namespace DittertRybin
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

noncomputable def fourRowMinorantSquareSum (r : Fin 4 → ℝ) : ℝ := ∑ i, r i ^ 2

noncomputable def fourRowMinorantDelta (r : Fin 4 → ℝ) : ℝ :=
  1 - 3 * fourRowMinorantSquareSum r

noncomputable def fourRowMinorantE3 (r : Fin 4 → ℝ) : ℝ :=
  ∑ i, ∏ j ∈ Finset.univ.erase i, r j

noncomputable def fourRowMinorantStationary (r : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  1 / 4 + r i * (fourRowMinorantSquareSum r - r i) / (2 * fourRowMinorantDelta r)

/-- The actual derivative with respect to one coordinate of v, before imposing sum r = 1. -/
noncomputable def fourRowMinorantGradient (r v : Fin 4 → ℝ) (i : Fin 4) : ℝ :=
  fourRowGaugeCollision r i - 4 * (∑ k, r k) *
    ∑ j ∈ Finset.univ.erase i, v j * ∏ k ∈ (Finset.univ.erase i).erase j, r k

/-- The source value e₂/4 − 3e₃/2 + P(4d−1)/(6d), using e₂=(1−q)/2. -/
noncomputable def fourRowMinorantStationaryValue (r : Fin 4 → ℝ) : ℝ :=
  (1 - fourRowMinorantSquareSum r) / 8 - (3 / 2) * fourRowMinorantE3 r +
    (∏ i, r i) * (4 * fourRowMinorantDelta r - 1) / (6 * fourRowMinorantDelta r)

theorem fourRowMinorantStationary_sum (r : Fin 4 → ℝ) (hs : ∑ i, r i = 1) :
    ∑ i, fourRowMinorantStationary r i = 1 := by
  have hcancel : (∑ i, r i * (fourRowMinorantSquareSum r - r i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul,
      ← pow_two, fourRowMinorantSquareSum, sub_self]
  simp only [fourRowMinorantStationary, Finset.sum_add_distrib, ← Finset.sum_div,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcancel, zero_div]
  norm_num

theorem fourRowMinorantE3_expand (r : Fin 4 → ℝ) :
    fourRowMinorantE3 r = r 0*r 1*r 2 + r 0*r 1*r 3 + r 0*r 2*r 3 + r 1*r 2*r 3 := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  norm_num [fourRowMinorantE3, Fin.sum_univ_four, hu, Finset.prod_insert,
    Finset.erase_insert, Finset.erase_insert_of_ne, Finset.erase_singleton,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  ring

/-- All four formal gradient coordinates agree at the stated stationary vector. -/
theorem fourRowMinorantStationary_gradient (r : Fin 4 → ℝ) (hs : ∑ i, r i = 1)
    (hd : fourRowMinorantDelta r ≠ 0) (i : Fin 4) :
    fourRowMinorantGradient r (fourRowMinorantStationary r) i =
      -fourRowMinorantE3 r - 2 * (∏ j, r j) / fourRowMinorantDelta r := by
  have hlast : r 3 = 1 - r 0 - r 1 - r 2 := by
    simp only [Fin.sum_univ_four] at hs
    linarith
  have hr : r = ![r 0, r 1, r 2, 1-r 0-r 1-r 2] := by
    funext j
    fin_cases j <;> simp [Matrix.cons_val_two, Matrix.cons_val_three, hlast]
  rw [hr] at hd ⊢
  norm_num [fourRowMinorantGradient, fourRowMinorantStationary,
    fourRowGaugeCollision_moments, fourRowMinorantE3_expand,
    fourRow_complement_product, Fin.sum_univ_succ, Fin.prod_univ_succ,
    Finset.sum_erase, Fin.ext_iff, -Fin.val_eq_zero_iff,
    Matrix.cons_val_two, Matrix.cons_val_three]
  fin_cases i <;> norm_num [Fin.ext_iff, -Fin.val_eq_zero_iff,
    Matrix.cons_val_two, Matrix.cons_val_three]
  all_goals
    field_simp [hd]
    norm_num [fourRowMinorantDelta, fourRowMinorantSquareSum, Fin.sum_univ_four,
      Matrix.cons_val_two, Matrix.cons_val_three]
    ring

/-- The exact objective value; nonnegative stationary coordinates are not automatic. -/
theorem fourRowMinorantStationary_value (r : Fin 4 → ℝ) (hs : ∑ i, r i = 1)
    (hd : fourRowMinorantDelta r ≠ 0) :
    fourRowMinorantHomogeneous r (fourRowMinorantStationary r) =
      fourRowMinorantStationaryValue r := by
  have hlast : r 3 = 1 - r 0 - r 1 - r 2 := by
    simp only [Fin.sum_univ_four] at hs
    linarith
  norm_num [fourRowMinorantHomogeneous, hs, fourRowMinorantStationary,
    fourRowMinorantStationaryValue, fourRowGaugeCollision_moments, hs,
    fourRowMinorantE3_expand, fourRow_complement_product,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Finset.sum_erase,
    Fin.ext_iff, -Fin.val_eq_zero_iff]
  field_simp [hd]
  simp only [fourRowMinorantDelta, fourRowMinorantSquareSum, Fin.sum_univ_four,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl, hlast]
  ring

end DittertRybin
