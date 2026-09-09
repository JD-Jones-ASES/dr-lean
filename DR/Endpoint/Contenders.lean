import DR.Endpoint.Normalization

/-!
# Actual rectangular endpoint contenders

The bounds apply to every nonnegative probability board whose m-sample
success is at least the uniform value. They first prove positivity of the
original row sums, and only then use the independent normalized-row law.
The exact shared deficit and collision-avoidance relation are the common
inputs of P0174's arithmetic and all-aspect-ratio endpoint arguments.
-/

namespace DittertRybin
open scoped BigOperators

theorem endpointRowProduct_nonneg {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ endpointRowProduct P := by
  rw [endpointRowProduct_eq_normalized]
  exact normalizedElementarySuccess_nonneg (rowSum_nonneg hP) _

theorem endpointRookRatio_nonneg {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ endpointRookRatio P := by
  rw [endpointRookRatio,rookSum_endpoint_eq_rowAvoidance]
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (rowAvoidance_nonneg P hP)

theorem endpointRowProduct_le_one {m n : ℕ} (hm : 2 ≤ m) {P : Board m n}
    (hP : IsProbability P) : endpointRowProduct P ≤ 1 := by
  rw [endpointRowProduct_eq_normalized]
  exact normalizedElementarySuccess_le_one (rowSum_nonneg hP.1) hP.2 hm le_rfl

theorem endpointColumnRatio_le_one {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P) : endpointColumnRatio P ≤ 1 := by
  apply normalizedElementarySuccess_le_one (colSum_nonneg hP.1) _ hm hmn
  exact (totalMass_eq_sum_colSum P).symm.trans hP.2

/-- Exact shared row/column deficit, on the closed probability simplex. -/
theorem endpoint_contender_deficit_budget {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    0 ≤ 1-endpointRowProduct P ∧ 0 ≤ 1-endpointColumnRatio P ∧
      (1-endpointRowProduct P)+
        (distinctUniformProbability n m/dittertConstant m)*(1-endpointColumnRatio P) ≤
          endpointRookDeficit P ∧
      0 ≤ endpointRookDeficit P ∧ endpointRookDeficit P ≤ distinctUniformProbability n m := by
  have hR := endpointRowProduct_le_one hm hP
  have hS := endpointColumnRatio_le_one hm hmn hP
  have hT := endpointRookRatio_nonneg hP.1
  have ha := endpoint_a_pos (by omega : 0 < m)
  have hb := distinctUniformProbability_pos (by omega : 0 < n) hmn
  rw [uniformSeparationValue_rectangular_endpoint,separationProbability_endpoint_ratios (by omega) hmn] at hcont
  have hbudget : (1-endpointRowProduct P)+
      (distinctUniformProbability n m/dittertConstant m)*(1-endpointColumnRatio P) ≤
        endpointRookDeficit P := by
    apply (mul_le_mul_iff_right₀ ha).mp
    have heq : dittertConstant m*((1-endpointRowProduct P)+
        (distinctUniformProbability n m/dittertConstant m)*(1-endpointColumnRatio P)) =
        dittertConstant m*(1-endpointRowProduct P)+
          distinctUniformProbability n m*(1-endpointColumnRatio P) := by field_simp
    rw [heq,endpointRookDeficit]
    nlinarith
  have hn := mul_nonneg (div_nonneg hb.le ha.le) (sub_nonneg.mpr hS)
  refine ⟨sub_nonneg.mpr hR,sub_nonneg.mpr hS,hbudget,by linarith,?_⟩
  unfold endpointRookDeficit
  linarith

theorem endpoint_contender_rowProduct_lower {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    1-distinctUniformProbability n m ≤ endpointRowProduct P := by
  have hS := endpointColumnRatio_le_one hm hmn hP
  have hT := endpointRookRatio_nonneg hP.1
  have ha := endpoint_a_pos (by omega : 0 < m)
  have hb := distinctUniformProbability_pos (by omega : 0 < n) hmn
  rw [uniformSeparationValue_rectangular_endpoint,separationProbability_endpoint_ratios (by omega) hmn] at hcont
  nlinarith [mul_nonneg ha.le hT,mul_le_mul_of_nonneg_left hS hb.le]

theorem endpoint_contender_columnRatio_lower {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    1-dittertConstant m ≤ endpointColumnRatio P := by
  have hR := endpointRowProduct_le_one hm hP
  have hT := endpointRookRatio_nonneg hP.1
  have ha := endpoint_a_pos (by omega : 0 < m)
  have hb := distinctUniformProbability_pos (by omega : 0 < n) hmn
  rw [uniformSeparationValue_rectangular_endpoint,separationProbability_endpoint_ratios (by omega) hmn] at hcont
  nlinarith [mul_nonneg ha.le hT,mul_le_mul_of_nonneg_left hR ha.le]

/-- Positive rows are derived before defining a normalized original-row probability law. -/
theorem endpoint_contender_rows_pos {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    ∀ i, 0 < rowSum P i := by
  have hR := endpoint_contender_rowProduct_lower hm hmn hP hcont
  have hb := distinctUniformProbability_lt_one (by omega : 0 < n) hm
  have hpos : 0 < endpointRowProduct P := by linarith
  have hprod : (∏ i, rowSum P i) ≠ 0 := by
    intro hz
    have hzR : endpointRowProduct P = 0 := by simp [endpointRowProduct,hz]
    linarith
  intro i
  have hi := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  exact lt_of_le_of_ne (rowSum_nonneg hP.1 i) hi.symm

/-- The original-row collision-avoidance inequality, with its denominator intact. -/
theorem endpoint_contender_original_collision_relation {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    1-distinctUniformProbability n m ≤ endpointRowProduct P*(1-originalRowAvoidance P) := by
  have hr := endpoint_contender_rows_pos hm hmn hP hcont
  have hS := endpointColumnRatio_le_one hm hmn hP
  have ha := endpoint_a_pos (by omega : 0 < m)
  have hb := distinctUniformProbability_pos (by omega : 0 < n) hmn
  rw [uniformSeparationValue_rectangular_endpoint,separationProbability_endpoint_ratios (by omega) hmn,
    endpointRookRatio_eq_originalRowAvoidance P (fun i => (hr i).ne')] at hcont
  nlinarith [mul_le_mul_of_nonneg_left hS hb.le]

/-- The original-row avoidance is an actual probability and is bounded by b. -/
theorem endpoint_contender_original_avoidance_bounds {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    0 ≤ originalRowAvoidance P ∧
      originalRowAvoidance P ≤ distinctUniformProbability n m ∧
      originalRowAvoidance P < 1 := by
  have hr := endpoint_contender_rows_pos hm hmn hP hcont
  have hp0 := rowAvoidance_nonneg (normalizeRows P) (normalizeRows_nonneg P hP.1)
  have hp1 := rowAvoidance_le_one (normalizeRows P) (normalizeRows_nonneg P hP.1)
    (normalizeRows_rowSum P (fun i => (hr i).ne'))
  change 0 ≤ originalRowAvoidance P at hp0
  change originalRowAvoidance P ≤ 1 at hp1
  have hR := endpointRowProduct_le_one hm hP
  have hrel := endpoint_contender_original_collision_relation hm hmn hP hcont
  have hpB : originalRowAvoidance P ≤ distinctUniformProbability n m := by
    nlinarith [mul_le_mul_of_nonneg_right hR (sub_nonneg.mpr hp1)]
  exact ⟨hp0,hpB,hpB.trans_lt (distinctUniformProbability_lt_one (by omega) hm)⟩

/-- Column concentration is derived from the actual contender, with zero columns allowed. -/
theorem endpoint_contender_columnVariance {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    marginalVariance (colSum P) ≤
      2*((n:ℝ)-1)*dittertConstant m/((n:ℝ)*m*(1-dittertConstant m)) := by
  exact marginalVariance_le_of_elementary_success (colSum_nonneg hP.1)
    ((totalMass_eq_sum_colSum P).symm.trans hP.2) hm hmn
    (endpoint_a_pos (by omega)).le (endpoint_a_lt_one hm)
    (endpoint_contender_columnRatio_lower hm hmn hP hcont)

theorem endpoint_contender_rowVariance {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    marginalVariance (rowSum P) ≤
      2*((m:ℝ)-1)*distinctUniformProbability n m/
        ((m:ℝ)*m*(1-distinctUniformProbability n m)) := by
  apply marginalVariance_le_of_elementary_success (rowSum_nonneg hP.1) hP.2 hm le_rfl
    (distinctUniformProbability_pos (by omega) hmn).le
    (distinctUniformProbability_lt_one (by omega) hm)
  rw [← endpointRowProduct_eq_normalized]
  exact endpoint_contender_rowProduct_lower hm hmn hP hcont

/-- The collision-avoidance factor cannot be dropped when improving the row product. -/
theorem endpoint_contender_rowProduct_deficit {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m) :
    1-endpointRowProduct P ≤
      (distinctUniformProbability n m-originalRowAvoidance P)/(1-originalRowAvoidance P) := by
  have hp := endpoint_contender_original_avoidance_bounds hm hmn hP hcont
  have hrel := endpoint_contender_original_collision_relation hm hmn hP hcont
  apply (le_div_iff₀ (sub_pos.mpr hp.2.2)).mpr
  nlinarith

end DittertRybin
