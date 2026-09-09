import DR.Endpoint.ElementaryLowerBound
import DR.Endpoint.FactorialScale
import DR.Endpoint.RowDeletionKernel
import DR.Endpoint.Contenders
import DR.Collision.Deletion

/-! The actual elementary coefficient dominates the independent-row
product scale. The no-collision probability remains in the denominator;
only its upper bound by one is used for this estimate. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_factorial_coefficient_guard {m : ℕ} (hm : 16≤m) :
    4*(m:ℝ)^2*(2:ℝ)^(m-2)*((m-2).factorial:ℝ)≤(m:ℝ)^m := by
  have hmR : (16:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have hf := Nat.factorial_mul_descFactorial (n:=m) (k:=2) (by omega)
  have hfact : (m.factorial:ℝ)=((m-2).factorial:ℝ)*(m:ℝ)*((m:ℝ)-1) := by
    have hcast := congrArg (fun q : ℕ => (q:ℝ)) hf
    simp only [Nat.cast_mul,Nat.descFactorial_succ,Nat.descFactorial_zero,Nat.cast_sub
      (by omega : 1≤m),Nat.cast_one,Nat.sub_zero,mul_one] at hcast
    nlinarith only [hcast]
  have hg := endpoint_scaled_factorial_lt_one_thirty_two hm
  rw [dittertConstant,← mul_div_assoc,div_lt_iff₀ (pow_pos hm0 m),hfact] at hg
  have hw : 0≤(2:ℝ)^(m-2)*((m-2).factorial:ℝ) := by positivity
  have hcomparison : 4*(m:ℝ)^2≤32*(m:ℝ)*((m:ℝ)-1) := by nlinarith
  have hc := mul_le_mul_of_nonneg_right hcomparison hw
  nlinarith only [hc,hg]

theorem endpoint_row_product_scale_le {m n : ℕ} (hm : 2≤m) (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hh : 0<totalMass P) :
    (∏ i,rowSum P i)/(totalMass P)^2≤
      (totalMass P)^(m-2)/(m:ℝ)^m := by
  have hm0 : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have h := endpointRowProduct_le_one hm (normalizeBoard_isProbability hP hh)
  simp only [endpointRowProduct,rowSum_normalizeBoard] at h
  have hprod : (∏ i,rowSum P i/totalMass P)≤1/(m:ℝ)^m := by
    apply (le_div_iff₀ (pow_pos hm0 m)).mpr
    nlinarith only [h]
  have hmul := mul_le_mul_of_nonneg_left hprod (pow_nonneg hh.le (m-2))
  rw [normalizedRow_product_coefficient hm (rowSum P) (totalMass P) hh.ne'] at hmul
  simpa only [mul_one_div] using hmul

/-- A cap on the actual retained columns discharges the fifth scalar field
of the endpoint kernel criterion. Zero entries are allowed throughout. -/
theorem endpoint_coefficient_ratio_lower {m n : ℕ} (hm : 16≤m) (P : Board m n)
    (hP : ∀ i j,0≤P i j) (hr : ∀ i,0<rowSum P i)
    (hh : 0<totalMass P) (hp : 0<rowAvoidance (normalizeRows P))
    (c : ℝ) (hc : ∀ j,colSum P j≤c)
    (hk : ((m-2:ℕ):ℝ)*c≤totalMass P/2) :
    4*(m:ℝ)^2≤averagingCoefficient P (m-2)/
      (((∏ i,rowSum P i)/(totalMass P)^2)*rowAvoidance (normalizeRows P)) := by
  let h := totalMass P
  let G := (∏ i,rowSum P i)/h^2
  let p := rowAvoidance (normalizeRows P)
  let k := m-2
  have hm0 : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hG : 0<G := div_pos (Finset.prod_pos (fun i _ => hr i)) (sq_pos_of_pos hh)
  have hp1 : p≤1 := rowAvoidance_le_one (normalizeRows P)
    (normalizeRows_nonneg P hP) (normalizeRows_rowSum P (fun i => (hr i).ne'))
  have hGp : G*p≤h^k/(m:ℝ)^m :=
    (mul_le_of_le_one_right hG.le hp1).trans (endpoint_row_product_scale_le (by omega) P hP hh)
  have hE := elementarySymmetric_lower_of_cap (colSum P) (colSum_nonneg hP)
    h c hh (totalMass_eq_sum_colSum P).symm hc hk
  have hf : 0<(k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hElower : h^k/((2:ℝ)^k*(k.factorial:ℝ))≤averagingCoefficient P k := by
    apply (div_le_iff₀ (mul_pos (by positivity) hf)).mpr
    have ht := mul_le_mul_of_nonneg_left hE (pow_nonneg (by norm_num : (0:ℝ)≤2) k)
    have he : (2:ℝ)^k*(h/2)^k=h^k := by rw [← mul_pow]; ring_nf
    rw [he] at ht
    change h^k≤(2:ℝ)^k*((k.factorial:ℝ)*averagingCoefficient P k) at ht
    nlinarith only [ht]
  have hguard := endpoint_factorial_coefficient_guard hm
  have hscale : 4*(m:ℝ)^2*(h^k/(m:ℝ)^m)≤h^k/((2:ℝ)^k*(k.factorial:ℝ)) := by
    apply (le_div_iff₀ (mul_pos (by positivity) hf)).mpr
    have ht := mul_le_mul_of_nonneg_right hguard
      (div_nonneg (pow_nonneg hh.le k) (pow_nonneg hm0.le m))
    have he : (m:ℝ)^m*(h^k/(m:ℝ)^m)=h^k := mul_div_cancel₀ _ (pow_ne_zero _ hm0.ne')
    rw [he] at ht
    convert ht using 1; ring
  apply (le_div_iff₀ (mul_pos hG hp)).mpr
  exact (mul_le_mul_of_nonneg_left hGp (by positivity)).trans (hscale.trans hElower)

end DittertRybin
