import DR.Square.FiveMarginalBounds
import DR.Endpoint.MarginalDiscrepancy

/-! Size-sensitive marginal geometry for the finite consecutive endpoint cuts.
The scalar logarithmic estimate retains the full positive interval up to H;
the centered-indicator projection is exact, including empty and full subsets. -/

namespace DittertRybin
open scoped BigOperators

/-- A capped positive coordinate has the source quadratic log-deficit lower bound. -/
theorem log_deficit_ge_sq_of_upper_cap {x H : ℝ} (hx : 0 < x)
    (hH : 1 ≤ H) (hxH : x ≤ H) :
    (x-1)^2/(2*H^2) ≤ x-1-Real.log x := by
  have hH0 : 0 < H := by linarith
  have hHsq : 1 ≤ H^2 := by nlinarith
  rcases le_total x 1 with hx1 | h1x
  · have h := log_deficit_ge_inverseVariance hx hx1 le_rfl
    have heq : x/2*((x-1)^2/x) = (x-1)^2/2 := by field_simp
    rw [heq] at h
    apply le_trans _ h
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by nlinarith)
  · have h := log_deficit_ge_inverseVariance (x := x) (by norm_num : (0 : ℝ) < 1) le_rfl h1x
    have heq : (1 : ℝ)/2*((x-1)^2/x) = (x-1)^2/(2*x) := by ring
    rw [heq] at h
    apply le_trans _ h
    have hxHsq : x ≤ H^2 := by nlinarith
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)

/-- Product deficit controls the entire centered square sum under the actual cap. -/
theorem capped_product_square_sum_le {d : ℕ} (x : Fin d → ℝ)
    (hx : ∀ i, 0 < x i) (hs : ∑ i, x i = d) {H rho b : ℝ}
    (hH : 1 ≤ H) (hcap : ∀ i, x i ≤ H)
    (hprod : ∏ i, x i = 1-rho) (hrho : 0 ≤ rho) (hrb : rho ≤ b) (hb : b < 1) :
    (∑ i, (x i-1)^2) ≤ 2*H^2*rho/(1-b) := by
  have hH0 : 0 < H := by linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    log_deficit_ge_sq_of_upper_cap (hx i) hH (hcap i)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hs, sub_self, zero_sub] at hsum
  rw [← Real.log_prod (fun i _ => (hx i).ne'), hprod] at hsum
  have h := hsum.trans (neg_log_one_sub_le hrho hrb hb)
  have hscaled := (div_le_iff₀ (by positivity : 0 < 2*H^2)).mp h
  exact hscaled.trans_eq (by ring)

/-- Exact orthogonal projection of a subset indicator onto the zero-sum space. -/
theorem probability_subset_sq_le_card_variance {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hs : ∑ i, x i = 1) (I : Finset (Fin d)) :
    ((∑ i ∈ I, x i)-I.card/(d : ℝ))^2 ≤
      (I.card : ℝ)*((d : ℝ)-I.card)/(d : ℝ)*marginalVariance x := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  let z : Fin d → ℝ := fun i => x i-1/(d : ℝ)
  let s : Fin d → ℝ := fun i => (if i ∈ I then 1 else 0)-I.card/(d : ℝ)
  have hz : ∑ i, z i = 0 := by simp [z, Finset.sum_sub_distrib, hs, hd0]
  have hI : (∑ i ∈ I, z i) = (∑ i ∈ I, x i)-I.card/(d : ℝ) := by
    simp [z, Finset.sum_sub_distrib, div_eq_mul_inv]
  have hind (f : Fin d → ℝ) : (∑ i, if i ∈ I then f i else 0) = ∑ i ∈ I, f i := by
    simp
  have hdot : (∑ i, s i*z i) = (∑ i ∈ I, x i)-I.card/(d : ℝ) := by
    simp only [s, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hz, mul_zero, sub_zero, hind, hI]
  have hterm (i : Fin d) : (s i)^2 =
      (if i ∈ I then 1 else 0)*(1-2*I.card/(d : ℝ))+(I.card/(d : ℝ))^2 := by
    by_cases hi : i ∈ I
    · simp only [s, if_pos hi]
      ring
    · simp only [s, if_neg hi]
      ring
  have hsq : (∑ i, (s i)^2) = (I.card : ℝ)*((d : ℝ)-I.card)/(d : ℝ) := by
    simp only [hterm, Finset.sum_add_distrib, ← Finset.sum_mul, hind, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    field_simp
    ring
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s z
  rw [hdot, hsq] at h
  exact h

end DittertRybin
