import DR.Endpoint.Contenders

/-!
# Endpoint marginal caps before a collision estimate

The column cap follows from closed-simplex Maclaurin. The original-row
product has a one-coordinate exponential envelope, proved directly by
1+t ≤ exp(t) on the other rows. These apply to actual contenders and are
common inputs to the transition and arithmetic endpoint strips.
-/

namespace DittertRybin
open scoped BigOperators

/-- A single coordinate is controlled by the complete centered squared norm. -/
theorem marginal_deviation_sq_le {d : ℕ} (x : Fin d → ℝ) (i : Fin d) :
    (x i-1/(d:ℝ))^2 ≤ marginalVariance x :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j-1/(d:ℝ))) (Finset.mem_univ i)

theorem marginal_coordinate_le {d : ℕ} (x : Fin d → ℝ) {v : ℝ}
    (hv : marginalVariance x ≤ v) (i : Fin d) : x i ≤ 1/(d:ℝ)+Real.sqrt v := by
  have hterm := (marginal_deviation_sq_le x i).trans hv
  have hv0 := (marginalVariance_nonneg x).trans hv
  have hs := Real.sq_sqrt hv0
  have hn := Real.sqrt_nonneg v
  nlinarith

/-- A dimension-free weakening of the exact column variance is convenient for strip estimates. -/
theorem endpoint_contender_columnVariance_simple {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    marginalVariance (colSum P) ≤ 2*dittertConstant m/((m:ℝ)*(1-dittertConstant m)) := by
  have hv := endpoint_contender_columnVariance hm hmn hP hcont
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha0 := endpoint_a_pos (by omega : 0 < m)
  have ha1 := endpoint_a_lt_one hm
  apply hv.trans
  apply (div_le_div_iff₀ (mul_pos (mul_pos hn0 hm0) (sub_pos.mpr ha1))
    (mul_pos hm0 (sub_pos.mpr ha1))).mpr
  nlinarith [mul_nonneg (mul_nonneg (show 0 ≤ (m:ℝ) from hm0.le) ha0.le)
    (sub_nonneg.mpr ha1.le)]

theorem endpoint_contender_column_cap {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) (j : Fin n) :
    colSum P j ≤ 1/(n:ℝ)+Real.sqrt (2*dittertConstant m/((m:ℝ)*(1-dittertConstant m))) :=
  marginal_coordinate_le _ (endpoint_contender_columnVariance_simple hm hmn hP hcont) j

/-- This row-product envelope allows zero coordinates and uses no stationarity. -/
theorem product_le_coordinate_mul_exp {d : ℕ} {y : Fin d → ℝ}
    (hy : ∀ i, 0 ≤ y i) (hs : ∑ i, y i = d) (i : Fin d) :
    (∏ j, y j) ≤ y i*Real.exp (1-y i) := by
  classical
  have hs' : (∑ j ∈ Finset.univ.erase i, (y j-1)) = 1-y i := by
    have h := Finset.sum_erase_add (Finset.univ : Finset (Fin d)) y (Finset.mem_univ i)
    rw [hs] at h
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_erase_of_mem
      (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    rw [Nat.cast_sub (by have := i.isLt; omega : 1 ≤ d)]
    norm_num only [Nat.cast_one]
    linarith
  have hprod : (∏ j ∈ Finset.univ.erase i, y j) ≤
      ∏ j ∈ Finset.univ.erase i, Real.exp (y j-1) := by
    apply Finset.prod_le_prod (fun j _ => hy j)
    intro j hj
    simpa only [sub_add_cancel] using Real.add_one_le_exp (y j-1)
  rw [← Real.exp_sum,hs'] at hprod
  have h := mul_le_mul_of_nonneg_left hprod (hy i)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact h

theorem endpointRowProduct_coordinate_envelope {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) (i : Fin m) :
    endpointRowProduct P ≤ (m:ℝ)*rowSum P i*Real.exp (1-(m:ℝ)*rowSum P i) := by
  rw [endpointRowProduct_eq_product]
  apply product_le_coordinate_mul_exp (fun i => mul_nonneg (Nat.cast_nonneg _) (rowSum_nonneg hP.1 i))
  simp only [← Finset.mul_sum]
  change (m:ℝ)*totalMass P = m
  rw [hP.2,mul_one]

/-- An explicit positive lower row cap, with the original uniform collision deficit. -/
theorem endpoint_contender_scaled_row_lower {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) (i : Fin m) :
    (1-distinctUniformProbability n m)/Real.exp 1 ≤ (m:ℝ)*rowSum P i := by
  have hR := endpoint_contender_rowProduct_lower hm hmn hP hcont
  have he := endpointRowProduct_coordinate_envelope hP i
  have hy := mul_nonneg (Nat.cast_nonneg m) (rowSum_nonneg hP.1 i)
  have hexp := Real.exp_le_exp.mpr (show 1-(m:ℝ)*rowSum P i ≤ 1 by linarith)
  have h := mul_le_mul_of_nonneg_left hexp hy
  exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by nlinarith)

end DittertRybin
