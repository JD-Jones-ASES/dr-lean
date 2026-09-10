import DR.Endpoint.ConsecutiveCutMarginals
import DR.Endpoint.CutDeficit

/-! The two size-sensitive marginal bounds consume the same actual rook
deficit. These are actual subset inequalities, before any finite cut-size
certificate or transport selection. -/

namespace DittertRybin
open scoped BigOperators

noncomputable def endpointSizedCutCoefficient (H : ℝ) (m n k l : ℕ) : ℝ :=
  (endpointSizedRowCutCoefficient H m k +
    (dittertConstant m/distinctUniformProbability n m)*endpointSizedColumnCutCoefficient m n l) /
    ((k : ℝ)/m+(l : ℝ)/n-1)^2

theorem endpoint_contender_sized_subset_discrepancy_sq {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    {H : ℝ} (hH : 1 ≤ H)
    (hcap : (m : ℝ)*distinctUniformProbability n m/(2*(1-distinctUniformProbability n m)) ≤
      (H-1)^2) (I : Finset (Fin m)) (J : Finset (Fin n)) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|)^2 ≤
      (endpointSizedRowCutCoefficient H m I.card +
        (dittertConstant m/distinctUniformProbability n m)*endpointSizedColumnCutCoefficient m n J.card)*
        endpointRookDeficit P/(1-distinctUniformProbability n m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : 0 ≤ (n : ℝ)-1 := by
    have h : (2 : ℝ) ≤ n := by exact_mod_cast (hm.trans hmn)
    linarith
  have hIc : (I.card : ℝ) ≤ m := by exact_mod_cast (show I.card ≤ m by simpa using I.card_le_univ)
  have hJc : (J.card : ℝ) ≤ n := by exact_mod_cast (show J.card ≤ n by simpa using J.card_le_univ)
  have hA : 0 ≤ endpointSizedRowCutCoefficient H m I.card := by
    unfold endpointSizedRowCutCoefficient
    positivity
  have hB : 0 ≤ endpointSizedColumnCutCoefficient m n J.card := by
    unfold endpointSizedColumnCutCoefficient
    positivity
  have ha := endpoint_a_pos (by omega : 0 < m)
  have hb := distinctUniformProbability_pos (by omega : 0 < n) hmn
  have hb1 := distinctUniformProbability_lt_one (by omega : 0 < n) hm
  have hden : 0 < 1-distinctUniformProbability n m := by linarith
  obtain ⟨hdr, hdc, hbudget, _, _⟩ := endpoint_contender_deficit_budget hm hmn hP hcont
  have hr := endpoint_contender_sized_row_subset_sq hm hmn hP hcont hH hcap I
  have hc := endpoint_contender_sized_column_subset_sq hm hmn hP hcont J
  have hrow : |(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)|^2 ≤
      (endpointSizedRowCutCoefficient H m I.card/(1-distinctUniformProbability n m))*
        (1-endpointRowProduct P) := by
    rw [sq_abs]
    exact hr.trans_eq (by ring)
  have hcol : |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|^2 ≤
      ((dittertConstant m/distinctUniformProbability n m)*endpointSizedColumnCutCoefficient m n J.card/
        (1-distinctUniformProbability n m))*
      ((distinctUniformProbability n m/dittertConstant m)*(1-endpointColumnRatio P)) := by
    rw [sq_abs]
    apply hc.trans_eq
    field_simp
  have hshared := add_sq_le_of_sq_le_mul (div_nonneg hA hden.le)
    (div_nonneg (mul_nonneg (div_nonneg ha.le hb.le) hB) hden.le) hdr
    (mul_nonneg (div_nonneg hb.le ha.le) hdc) hrow hcol
  have hcoef : 0 ≤ endpointSizedRowCutCoefficient H m I.card/(1-distinctUniformProbability n m)+
      (dittertConstant m/distinctUniformProbability n m)*endpointSizedColumnCutCoefficient m n J.card/
        (1-distinctUniformProbability n m) := by positivity
  apply hshared.trans ((mul_le_mul_of_nonneg_left hbudget hcoef).trans_eq ?_)
  ring

/-- The active-cut coefficient is tied to actual marginal subsets with its exact demand square. -/
theorem endpoint_contender_sized_cut_discrepancy_sq {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    {H : ℝ} (hH : 1 ≤ H)
    (hcap : (m : ℝ)*distinctUniformProbability n m/(2*(1-distinctUniformProbability n m)) ≤
      (H-1)^2) (I : Finset (Fin m)) (J : Finset (Fin n))
    (hp : 0 < (I.card : ℝ)/m+(J.card : ℝ)/n-1) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|)^2 ≤
      ((I.card : ℝ)/m+(J.card : ℝ)/n-1)^2 *
        endpointSizedCutCoefficient H m n I.card J.card*endpointRookDeficit P /
        (1-distinctUniformProbability n m) := by
  apply (endpoint_contender_sized_subset_discrepancy_sq hm hmn hP hcont hH hcap I J).trans_eq
  unfold endpointSizedCutCoefficient
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 hp.ne')]

end DittertRybin
