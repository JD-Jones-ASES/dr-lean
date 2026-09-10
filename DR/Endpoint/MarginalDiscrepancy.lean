import DR.Square.MarginalDiscrepancy
import DR.Endpoint.Contenders
import DR.Endpoint.FactorialDecay

/-! Sharp shared marginal control for rectangular endpoint contenders.
The row estimate reuses the proved binary entropy inequality. The column
estimate uses closed-simplex Maclaurin stability and a centered sign vector.
Every subset is retained, including empty and full subsets. -/

namespace DittertRybin
open scoped BigOperators

/-- Cauchy--Schwarz with a centered sign vector retains the factor four. -/
theorem probability_subset_sq_le_variance {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (hs : ∑ i, x i = 1) (I : Finset (Fin d)) :
    ((∑ i ∈ I, x i) - I.card / (d : ℝ))^2 ≤
      (d : ℝ) * marginalVariance x / 4 := by
  classical
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  let z := fun i => x i - 1/(d : ℝ)
  have hsum : ∑ i, z i = 0 := by
    simp [z, Finset.sum_sub_distrib, hs, hd0]
  have hI : (∑ i ∈ I, z i) = (∑ i ∈ I, x i) - I.card / (d : ℝ) := by
    simp [z, Finset.sum_sub_distrib, div_eq_mul_inv]
  have hcomp : (∑ i ∈ Iᶜ, z i) = -(∑ i ∈ I, z i) := by
    have h := Finset.sum_add_sum_compl I z
    rw [hsum] at h
    linarith
  let s : Fin d → ℝ := fun i => if i ∈ I then 1 else -1
  have hsign : ∑ i, s i * z i = 2 * ∑ i ∈ I, z i := by
    rw [← Finset.sum_add_sum_compl I (fun i => s i * z i)]
    have hleft : (∑ i ∈ I, s i * z i) = ∑ i ∈ I, z i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [s, hi]
    have hright : (∑ i ∈ Iᶜ, s i * z i) = -(∑ i ∈ Iᶜ, z i) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      simp [s, Finset.mem_compl.mp hi]
    rw [hleft, hright, hcomp]
    ring
  have hsquare : (∑ i, (s i)^2) = d := by
    have he (i : Fin d) : (s i)^2 = 1 := by
      dsimp [s]
      split <;> norm_num
    simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ s z
  rw [hsign, hsquare, hI] at h
  change (2 * ((∑ i ∈ I, x i) - I.card / (d : ℝ)))^2 ≤
    (d : ℝ) * marginalVariance x at h
  nlinarith only [h]

/-- Endpoint row products give a dimension-sharp bound for every subset. -/
theorem endpoint_row_subset_sq {m n : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    (hb : distinctUniformProbability n m ≤ 1/4) (I : Finset (Fin m)) :
    ((∑ i ∈ I, rowSum P i) - I.card / (m : ℝ))^2 ≤
      2 * (1-endpointRowProduct P) / (3*m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hr := endpoint_contender_rows_pos hm hmn hP hcont
  obtain ⟨hdr, hdc, hbudget, hd0, hdb⟩ :=
    endpoint_contender_deficit_budget hm hmn hP hcont
  have ha := endpoint_a_pos (by omega : 0 < m)
  have hb0 := distinctUniformProbability_pos (by omega : 0 < n) hmn
  have hdrb : 1-endpointRowProduct P ≤ 1/4 := by
    have hnonneg := mul_nonneg (div_nonneg hb0.le ha.le) hdc
    linarith
  have hs : (∑ i, (m : ℝ)*rowSum P i) = m := by
    rw [← Finset.mul_sum]
    change (m : ℝ)*totalMass P = m
    rw [hP.2, mul_one]
  have hprod : (∏ i, (m : ℝ)*rowSum P i) = 1-(1-endpointRowProduct P) := by
    rw [← endpointRowProduct_eq_product]
    ring
  have h := subset_discrepancy_sq_le (by omega : 0 < m)
    (fun i => (m : ℝ)*rowSum P i) (fun i => mul_pos hm0 (hr i)) hs
    hprod hdr hdrb (by norm_num : (1/4 : ℝ) < 1) I
  have hid : (∑ i ∈ I, (m : ℝ)*rowSum P i) - I.card =
      (m : ℝ)*((∑ i ∈ I, rowSum P i) - I.card / (m : ℝ)) := by
    rw [← Finset.mul_sum]
    field_simp
  rw [hid] at h
  have h' : (m : ℝ)^2 * ((∑ i ∈ I, rowSum P i) - I.card / (m : ℝ))^2 ≤
      (m : ℝ)^2 * (2*(1-endpointRowProduct P)/(3*m)) := by
    convert h using 1
    · ring
    · field_simp
      ring
  exact (mul_le_mul_iff_right₀ (pow_pos hm0 2)).mp h'

/-- Closed-simplex elementary success controls every subset, even with zeros. -/
theorem elementary_subset_sq_le {d k : ℕ} {x : Fin d → ℝ}
    (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1) (hk : 2 ≤ k) (hkd : k ≤ d)
    {epsilon : ℝ} (he0 : 0 ≤ epsilon) (he1 : epsilon ≤ 1/4)
    (he : 1-epsilon ≤ normalizedElementarySuccess x k) (I : Finset (Fin d)) :
    ((∑ i ∈ I, x i) - I.card / (d : ℝ))^2 ≤
      2*((d : ℝ)-1)*epsilon/(3*k) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hd1 : 0 ≤ (d : ℝ)-1 := by
    have h : (2 : ℝ) ≤ d := by exact_mod_cast (hk.trans hkd)
    linarith
  have hepos : 0 < 1-epsilon := by linarith
  have hv := marginalVariance_le_of_elementary_success hx hs hk hkd he0
    (by linarith : epsilon < 1) he
  have hI := probability_subset_sq_le_variance (by omega) x hs I
  have hb := mul_le_mul_of_nonneg_left hv (div_nonneg hd0.le (by norm_num : (0 : ℝ) ≤ 4))
  have hleft : (d : ℝ)/4*marginalVariance x = d*marginalVariance x/4 := by ring
  rw [hleft] at hb
  apply hI.trans (hb.trans ?_)
  have hnonneg : 0 ≤ ((d : ℝ)-1)*epsilon := mul_nonneg hd1 he0
  field_simp
  nlinarith only [mul_nonneg hnonneg (show 0 ≤ 1-4*epsilon by linarith)]

/-- The elementary factorial bound is sufficient from three rows. -/
theorem endpoint_a_le_quarter {m : ℕ} (hm : 3 ≤ m) :
    dittertConstant m ≤ 1/4 := by
  rw [← distinctUniformProbability_self]
  apply (distinctUniformProbability_endpoint_le_half_pow (by omega)).trans
  have h : (1/2 : ℝ)^(m-1) ≤ (1/2 : ℝ)^2 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at h ⊢
  exact h

/-- A weighted two-coordinate Cauchy bound with a shared deficit budget. -/
theorem shared_weighted_discrepancy_sq {x y A v r s delta : ℝ}
    (hA : 0 ≤ A) (hv : 0 < v)
    (hx : x^2 ≤ A*r) (hy : y^2 ≤ A*v*s) (hbudget : r+s ≤ delta) :
    (x+y)^2 ≤ A*(1+v)*delta := by
  have hY : y^2/v ≤ A*s := by
    apply (div_le_iff₀ hv).mpr
    nlinarith only [hy]
  have hweighted : (x+y)^2 ≤ (1+v)*(x^2+y^2/v) := by
    apply (mul_le_mul_iff_right₀ hv).mp
    have hid : v*((1+v)*(x^2+y^2/v)-(x+y)^2) = (v*x-y)^2 := by
      field_simp
      ring
    nlinarith only [hid, sq_nonneg (v*x-y)]
  have hsum : x^2+y^2/v ≤ A*delta := by
    nlinarith only [hx, hY, mul_le_mul_of_nonneg_left hbudget hA]
  exact hweighted.trans (by
    have h := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 1+v by linarith)
    nlinarith only [h])

/-- The actual shared rectangular endpoint estimate, for every pair of subsets.
The row and column deficits consume one common rook-deficit budget. -/
theorem endpoint_contender_subset_discrepancy_sq {m n : ℕ}
    (hm : 3 ≤ m) (hmn : m ≤ n) {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m ≤ separationProbability P m)
    (hb : distinctUniformProbability n m ≤ 1/4)
    (I : Finset (Fin m)) (J : Finset (Fin n)) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(m : ℝ)| +
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|)^2 ≤
    (2/(3*(m : ℝ)))*(1+((n : ℝ)-1)*dittertConstant m/distinctUniformProbability n m)*
      endpointRookDeficit P := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn1 : (0 : ℝ) < (n : ℝ)-1 := by
    have h : (3 : ℝ) ≤ n := by exact_mod_cast (hm.trans hmn)
    linarith
  have ha0 := endpoint_a_pos (by omega : 0 < m)
  have hb0 := distinctUniformProbability_pos (by omega : 0 < n) hmn
  obtain ⟨hdr, hdc, hbudget, _hd0, _hdb⟩ :=
    endpoint_contender_deficit_budget (by omega) hmn hP hcont
  have hdc4 : 1-endpointColumnRatio P ≤ 1/4 := by
    have h := endpoint_contender_columnRatio_lower (by omega) hmn hP hcont
    have ha := endpoint_a_le_quarter hm
    linarith
  have hr := endpoint_row_subset_sq (by omega) hmn hP hcont hb I
  have hc := elementary_subset_sq_le (colSum_nonneg hP.1)
    ((totalMass_eq_sum_colSum P).symm.trans hP.2) (by omega : 2 ≤ m) hmn hdc hdc4
    (by change 1-(1-endpointColumnRatio P) ≤ endpointColumnRatio P; linarith) J
  have hv : 0 < ((n : ℝ)-1)*dittertConstant m/distinctUniformProbability n m :=
    div_pos (mul_pos hn1 ha0) hb0
  apply shared_weighted_discrepancy_sq (by positivity) hv _ _ hbudget
  · rw [sq_abs]
    convert hr using 1; ring
  · rw [sq_abs]
    convert hc using 1
    field_simp

end DittertRybin
