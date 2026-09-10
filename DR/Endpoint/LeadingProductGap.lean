import DR.Endpoint.LeadingNorm
import DR.Endpoint.RowProductConcentration
import DR.Square.Contenders

/-! Product stability after the twice-uniform row cap, and the resulting
quantitative norm gap. The cap and PSD hypotheses are explicit here; their
derivation at an actual saturated minimum is separate. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

theorem endpoint_capped_product_exp {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0<y i) (hc : ∀ i,y i≤2) (hs : ∑ i,y i=d) :
    (∏ i,y i)≤Real.exp (-(∑ i,(y i-1)^2)/8) := by
  have h := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    log_le_sub_one_sub_sq_eighth (y i) (hy i) (hc i))
  have hl : (∑ i,Real.log (y i))=Real.log (∏ i,y i) :=
    (Real.log_prod (fun i _ => (hy i).ne')).symm
  have he : (∑ i,(y i-1))=0 := by
    simp only [Finset.sum_sub_distrib,hs,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one,sub_self]
  rw [hl,Finset.sum_sub_distrib,he,← Finset.sum_div,zero_sub] at h
  simpa only [Real.exp_log (Finset.prod_pos (fun i _ => hy i)),neg_div] using
    Real.exp_le_exp.mpr h

theorem endpoint_scaled_variance {m : ℕ} (hm : 0<m) (r : Fin m → ℝ) :
    (∑ i,((m:ℝ)*r i-1)^2)=(m:ℝ)^2*marginalVariance r := by
  unfold marginalVariance
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp

theorem endpoint_factorial_product_scaled {m : ℕ} (hm : 0<m) (r : Fin m → ℝ) :
    (m.factorial:ℝ)*∏ i,r i=dittertConstant m*(∏ i,(m:ℝ)*r i) := by
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,dittertConstant]
  have hmR : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  field_simp

theorem endpoint_marginal_product_exp {m : ℕ} (hm : 0<m) (r : Fin m → ℝ)
    (hr : ∀ i,0<r i) (hs : ∑ i,r i=1) (hc : ∀ i,r i≤2/(m:ℝ)) :
    (m.factorial:ℝ)*∏ i,r i≤
      dittertConstant m*Real.exp (-((m:ℝ)^2*marginalVariance r)/8) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have h := endpoint_capped_product_exp (fun i => (m:ℝ)*r i)
    (fun i => mul_pos hmR (hr i)) (fun i => by
      have hi := (le_div_iff₀ hmR).mp (hc i)
      nlinarith only [hi]) (by rw [← Finset.mul_sum,hs,mul_one])
  rw [endpoint_scaled_variance hm r] at h
  rw [endpoint_factorial_product_scaled hm r]
  exact mul_le_mul_of_nonneg_left h (dittertConstant_pos hm).le

theorem endpoint_one_sub_exp_lower {x : ℝ} (hx : 0≤x) :
    x/(8*(1+x))≤1-Real.exp (-x/8) := by
  have hd : 0<8*(1+x) := by positivity
  have he : Real.exp (-x/8)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (x/8))
    (Real.exp_pos (-x/8)).le
  have hid : Real.exp (x/8)*Real.exp (-x/8)=1 := by
    rw [← Real.exp_add]
    have heq : x/8+(-x/8)=0 := by ring
    rw [heq,Real.exp_zero]
  rw [hid] at h
  apply (div_le_iff₀ hd).mpr
  nlinarith only [h,mul_nonneg hx (sub_nonneg.mpr he)]

/-- A uniform rational norm gap, with no small-variance hypothesis. -/
theorem endpoint_sqrt_exp_gap {a x : ℝ} (ha : 0≤a) (ha1 : a≤1) (hx : 0≤x) :
    a*x/(16*(1+x))≤Real.sqrt (1-a*Real.exp (-x/8))-Real.sqrt (1-a) := by
  let e := Real.exp (-x/8)
  let u := Real.sqrt (1-a*e)
  let v := Real.sqrt (1-a)
  have he0 : 0≤e := (Real.exp_pos _).le
  have he1 : e≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hrad : 0≤1-a*e := by nlinarith only [ha1,mul_nonneg ha (sub_nonneg.mpr he1)]
  have hu2 : u^2=1-a*e := Real.sq_sqrt hrad
  have hv2 : v^2=1-a := Real.sq_sqrt (by linarith)
  have hu0 : 0≤u := Real.sqrt_nonneg _
  have hv0 : 0≤v := Real.sqrt_nonneg _
  have hu1 : u≤1 := by nlinarith only [hu2,hu0,mul_nonneg ha he0]
  have hv1 : v≤1 := by nlinarith only [hv2,hv0,ha]
  have huv : v≤u := Real.sqrt_le_sqrt (by nlinarith only [mul_nonneg ha (sub_nonneg.mpr he1)])
  have hgap : a*(1-e)≤2*(u-v) := by
    nlinarith only [hu2,hv2,mul_nonneg (sub_nonneg.mpr huv) (show 0≤2-u-v by linarith)]
  have h := mul_le_mul_of_nonneg_left (endpoint_one_sub_exp_lower hx) ha
  change a*(x/(8*(1+x)))≤a*(1-e) at h
  have hid : a*(x/(8*(1+x)))=2*(a*x/(16*(1+x))) := by
    field_simp
    ring
  rw [hid] at h
  change _≤u-v
  linarith

/-- Quantitative leading gauge at an actual board with its original PSD kernel. -/
theorem endpointLeadingGauge_saturated_norm_gap {m n : ℕ} (hm : 2≤m) (P : Board m n)
    (hP : IsProbability P) (hr : ∀ i,0<rowSum P i)
    (hc : ∀ i,rowSum P i≤2/(m:ℝ))
    (hQ : (endpointLeadingKernel (rowSum P)).PosSemidef) :
    dittertConstant m*((m:ℝ)^2*marginalVariance (rowSum P))/
      (16*(1+(m:ℝ)^2*marginalVariance (rowSum P)))≤
        endpointLeadingGauge P-Real.sqrt (1-dittertConstant m) := by
  have hm0 : 0<m := by omega
  have hp := endpoint_marginal_product_exp hm0 (rowSum P) hr hP.2 hc
  have hnorm := endpointLeadingGauge_product_lower hm P hP hQ
  have hsqrt := Real.sqrt_le_sqrt (show
      1-dittertConstant m*Real.exp (-((m:ℝ)^2*marginalVariance (rowSum P))/8)≤
      1-(m.factorial:ℝ)*∏ i,rowSum P i by linarith)
  have hgap := endpoint_sqrt_exp_gap (x:=(m:ℝ)^2*marginalVariance (rowSum P))
    (dittertConstant_pos hm0).le (dittertConstant_lt_one hm).le
    (mul_nonneg (sq_nonneg _) (marginalVariance_nonneg _))
  linarith

end DittertRybin
