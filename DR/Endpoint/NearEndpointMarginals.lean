import DR.Endpoint.NearEndpointNormalization
import DR.Endpoint.MarginalDiscrepancy
import DR.Endpoint.CutDeficit

/-! Near-endpoint contender marginals and actual balanced domination. These
are unconditional matrix estimates under explicit scalar size bounds; no
permanent gap or desired optimizer is assumed. -/
namespace DittertRybin
open scoped BigOperators

/-- For n−1 draws, every marginal subset has squared discrepancy at most
2/3 of its own normalized elementary deficit. -/
theorem nearEndpoint_elementary_subset_sq {n : ℕ} (hn : 3 ≤ n)
    {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) (hs : ∑ i, x i = 1)
    {ε : ℝ} (he0 : 0 ≤ ε) (he1 : ε ≤ 1/4)
    (he : 1-ε ≤ normalizedElementarySuccess x (n-1)) (I : Finset (Fin n)) :
    ((∑ i ∈ I, x i)-I.card/(n : ℝ))^2 ≤ (2/3 : ℝ)*ε := by
  have h := elementary_subset_sq_le hx hs (by omega : 2 ≤ n-1)
    (Nat.sub_le n 1) he0 he1 he I
  have hn1 : (n : ℝ)-1 ≠ 0 := by
    have h : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have heq : 2*((n : ℝ)-1)*ε/(3*(n-1 : ℕ)) = (2/3 : ℝ)*ε := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    field_simp
  rwa [heq] at h

/-- Actual row and column discrepancies use one common deficit budget. -/
theorem nearEndpoint_contender_subset_discrepancy_sq {n : ℕ} (hn : 3 ≤ n)
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (ha : distinctUniformProbability n (n-1) ≤ 1/4)
    (I J : Finset (Fin n)) :
    (|(∑ i ∈ I, rowSum P i)-I.card/(n : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|)^2 ≤ (4/3 : ℝ)*nearEndpointRookDeficit P := by
  obtain ⟨hdr,hdc,hbudget,_hd,hda⟩ := nearEndpoint_contender_deficit_budget hn hP hcont
  have hr := nearEndpoint_elementary_subset_sq hn (rowSum_nonneg hP.1) hP.2
    hdr (by linarith : 1-nearEndpointRowRatio P ≤ 1/4) (by simp [nearEndpointRowRatio]) I
  have hc := nearEndpoint_elementary_subset_sq hn (colSum_nonneg hP.1)
    ((totalMass_eq_sum_colSum P).symm.trans hP.2)
    hdc (by linarith : 1-nearEndpointColumnRatio P ≤ 1/4) (by simp [nearEndpointColumnRatio]) J
  have h := shared_weighted_discrepancy_sq (x := |(∑ i ∈ I, rowSum P i)-I.card/(n : ℝ)|)
    (y := |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)|) (A := (2/3 : ℝ)) (v := 1)
    (by norm_num) (by norm_num) (by simpa only [sq_abs] using hr)
    (by simpa only [sq_abs, mul_one] using hc) hbudget
  norm_num at h ⊢
  exact h

/-- The square cut grid yields an actual balanced board below the scaled
contender. The scale is exactly t²=(4/3)n²δ, including δ=0. -/
theorem nearEndpoint_contender_exists_balanced_domination {n : ℕ} (hn : 3 ≤ n)
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1))
    (ha : distinctUniformProbability n (n-1) ≤ 1/4)
    (hsize : (4/3 : ℝ)*(n : ℝ)^2*distinctUniformProbability n (n-1) < 1) :
    ∃ (t : ℝ) (B : Board n n), 0 ≤ t ∧ t < 1 ∧
      t^2 = (4/3 : ℝ)*(n : ℝ)^2*nearEndpointRookDeficit P ∧ IsProbability B ∧
      (∀ i, rowSum B i = 1/(n : ℝ)) ∧ (∀ j, colSum B j = 1/(n : ℝ)) ∧
      ∀ i j, (1-t)*B i j ≤ P i j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨_,_,_,hd,hda⟩ := nearEndpoint_contender_deficit_budget hn hP hcont
  let t : ℝ := Real.sqrt ((4/3 : ℝ)*(n : ℝ)^2*nearEndpointRookDeficit P)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have htsq : t^2 = (4/3 : ℝ)*(n : ℝ)^2*nearEndpointRookDeficit P :=
    Real.sq_sqrt (by positivity)
  have ht1 : t < 1 := by
    have hb := (mul_le_mul_of_nonneg_left hda
      (show 0 ≤ (4/3 : ℝ)*(n : ℝ)^2 by positivity)).trans_lt hsize
    nlinarith only [hb,htsq,ht]
  have hdev (I J : Finset (Fin n)) :
      |(∑ i ∈ I, rowSum P i)-I.card/(n : ℝ)|+
      |(∑ j ∈ J, colSum P j)-J.card/(n : ℝ)| ≤ t*(n : ℝ)/((n : ℝ)*n) := by
    have hs := nearEndpoint_contender_subset_discrepancy_sq hn hP hcont ha I J
    have hid : (t*(n : ℝ)/((n : ℝ)*n))^2 = (4/3 : ℝ)*nearEndpointRookDeficit P := by
      calc
        _ = t^2/(n : ℝ)^2 := by field_simp
        _ = _ := by rw [htsq]; field_simp
    have hnonneg : 0 ≤ t*(n : ℝ)/((n : ℝ)*n) := by positivity
    nlinarith only [hs,hid,hnonneg]
  obtain ⟨B,hB,hr,hc,hdom⟩ := exists_balanced_dominated_of_subset_discrepancy
    (by omega) (by omega) (dvd_refl n) (dvd_refl n) hP ht ht1 hdev
  exact ⟨t,B,ht,ht1,htsq,hB,hr,hc,hdom⟩

end DittertRybin
