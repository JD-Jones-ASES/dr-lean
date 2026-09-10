import DR.Endpoint.ConsecutiveCutGeometry
import DR.Endpoint.DoubleRecurrence
import DR.Square.SixMarginalBounds

/-! Actual size-sensitive row and column bounds for rectangular endpoint
contenders. The row cap is obtained from the product-deficit theorem;
the column bound retains the existing closed-simplex Maclaurin estimate. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def endpointSizedRowCutCoefficient (H : ℝ) (m k : ℕ) : ℝ :=
  2*H^2*(k : ℝ)*((m : ℝ)-k)/(m : ℝ)^3

noncomputable def endpointSizedColumnCutCoefficient (m n l : ℕ) : ℝ :=
  2*((n : ℝ)-1)*(l : ℝ)*((n : ℝ)-l)/((n : ℝ)^2*m)

theorem probability_product_variance_le_of_cap {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hx : ∀ i, 0 < x i) (hs : ∑ i, x i = 1)
    {H rho b : ℝ} (hH : 1 ≤ H) (hcap : ∀ i, (d : ℝ)*x i ≤ H)
    (hprod : ∏ i, (d : ℝ)*x i = 1-rho)
    (hrho : 0 ≤ rho) (hrb : rho ≤ b) (hb : b < 1) :
    marginalVariance x ≤ 2*H^2*rho/((d : ℝ)^2*(1-b)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hb0 : 0 < 1-b := by linarith
  have hsX : (∑ i, (d : ℝ)*x i) = d := by rw [← Finset.mul_sum, hs, mul_one]
  have hV := capped_product_square_sum_le (fun i => (d : ℝ)*x i)
    (fun i => mul_pos hdR (hx i)) hsX hH hcap hprod hrho hrb hb
  have hid : (∑ i, ((d : ℝ)*x i-1)^2) = (d : ℝ)^2*marginalVariance x := by
    rw [marginalVariance, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [hid] at hV
  apply (le_div_iff₀ (mul_pos (pow_pos hdR 2) hb0)).mpr
  have h := (le_div_iff₀ hb0).mp hV
  nlinarith only [h]

theorem endpoint_contender_row_variance_of_cap {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    {H : ℝ} (hH : 1 ≤ H)
    (hcap : (m : ℝ)*distinctUniformProbability n m/(2*(1-distinctUniformProbability n m)) ≤
      (H-1)^2) :
    marginalVariance (rowSum P) ≤
      2*H^2*(1-endpointRowProduct P)/((m : ℝ)^2*(1-distinctUniformProbability n m)) := by
  have hm0 : 0 < m := by omega
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hb := distinctUniformProbability_lt_one (by omega : 0 < n) hm
  have hrow := endpoint_contender_rows_pos hm hmn hP hcont
  have hbudget := endpoint_contender_deficit_budget hm hmn hP hcont
  have hrb : 1-endpointRowProduct P ≤ distinctUniformProbability n m := by
    linarith [endpoint_contender_rowProduct_lower hm hmn hP hcont]
  have hs : (∑ i, rowSum P i) = 1 := hP.2
  have hsX : (∑ i, (m : ℝ)*rowSum P i) = m := by rw [← Finset.mul_sum, hs, mul_one]
  have hprod : (∏ i, (m : ℝ)*rowSum P i) = 1-(1-endpointRowProduct P) := by
    rw [← endpointRowProduct_eq_product]
    ring
  have hupper (i : Fin m) : (m : ℝ)*rowSum P i ≤ H :=
    marginal_le_of_deficit_cap hm0 (fun i => (m : ℝ)*rowSum P i)
      (fun i => mul_pos hmR (hrow i)) hsX hprod hbudget.1 hrb hb hH hcap i
  exact probability_product_variance_le_of_cap hm0 (rowSum P) hrow hs hH hupper
    hprod hbudget.1 hrb hb

theorem endpoint_contender_sized_row_subset_sq {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    {H : ℝ} (hH : 1 ≤ H)
    (hcap : (m : ℝ)*distinctUniformProbability n m/(2*(1-distinctUniformProbability n m)) ≤
      (H-1)^2) (I : Finset (Fin m)) :
    ((∑ i ∈ I, rowSum P i)-I.card/(m : ℝ))^2 ≤
      endpointSizedRowCutCoefficient H m I.card*(1-endpointRowProduct P)/(1-distinctUniformProbability n m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hIcard : (I.card : ℝ) ≤ m := by exact_mod_cast (show I.card ≤ m by simpa using I.card_le_univ)
  have hcoef : 0 ≤ (I.card : ℝ)*((m : ℝ)-I.card)/(m : ℝ) := by positivity
  have hproj := probability_subset_sq_le_card_variance (by omega : 0 < m)
    (rowSum P) hP.2 I
  have hvar := endpoint_contender_row_variance_of_cap hm hmn hP hcont hH hcap
  apply hproj.trans ((mul_le_mul_of_nonneg_left hvar hcoef).trans_eq ?_)
  unfold endpointSizedRowCutCoefficient
  field_simp

theorem endpoint_contender_column_variance {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    marginalVariance (colSum P) ≤
      2*((n : ℝ)-1)*(1-endpointColumnRatio P)/((n : ℝ)*m*(1-distinctUniformProbability n m)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn1 : 0 ≤ (n : ℝ)-1 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (hm.trans hmn)
    linarith
  have hb := distinctUniformProbability_lt_one (by omega : 0 < n) hm
  have hdc := (endpoint_contender_deficit_budget hm hmn hP hcont).2.1
  have hab : dittertConstant m ≤ distinctUniformProbability n m := by
    simpa only [distinctUniformProbability_self] using
      distinctUniformProbability_mono_columns (by omega : 0 < m) (le_refl m) hmn
  have hdcb : 1-endpointColumnRatio P ≤ distinctUniformProbability n m := by
    linarith [endpoint_contender_columnRatio_lower hm hmn hP hcont]
  have hv := marginalVariance_le_of_elementary_success (colSum_nonneg hP.1)
    ((totalMass_eq_sum_colSum P).symm.trans hP.2) hm hmn hdc
    (by linarith : 1-endpointColumnRatio P < 1)
    (by change 1-(1-endpointColumnRatio P) ≤ endpointColumnRatio P; linarith)
  apply hv.trans
  exact div_le_div_of_nonneg_left (by positivity)
    (by positivity : 0 < (n : ℝ)*m*(1-distinctUniformProbability n m))
    (by gcongr)

theorem endpoint_contender_sized_column_subset_sq {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    (J : Finset (Fin n)) :
    ((∑ j ∈ J, colSum P j)-J.card/(n : ℝ))^2 ≤
      endpointSizedColumnCutCoefficient m n J.card*(1-endpointColumnRatio P)/(1-distinctUniformProbability n m) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hJcard : (J.card : ℝ) ≤ n := by exact_mod_cast (show J.card ≤ n by simpa using J.card_le_univ)
  have hcoef : 0 ≤ (J.card : ℝ)*((n : ℝ)-J.card)/(n : ℝ) := by positivity
  have hproj := probability_subset_sq_le_card_variance (by omega : 0 < n)
    (colSum P) ((totalMass_eq_sum_colSum P).symm.trans hP.2) J
  have hvar := endpoint_contender_column_variance hm hmn hP hcont
  apply hproj.trans ((mul_le_mul_of_nonneg_left hvar hcoef).trans_eq ?_)
  unfold endpointSizedColumnCutCoefficient
  field_simp

end DittertRybin
