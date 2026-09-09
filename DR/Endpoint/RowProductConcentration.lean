import DR.Endpoint.Caps
import DR.Endpoint.RowCollisionLogBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Dimension-free row concentration from the actual product deficit.
This is ENDPOINT_LLL_STRIP, Section 1. The quadratic logarithm estimate
is proved from log(sqrt y)≤sqrt y−1, retaining the full closed upper cap. -/

namespace DittertRybin
open scoped BigOperators

theorem log_le_sub_one_sub_sq_eighth (y : ℝ) (hy : 0<y) (hy2 : y≤2) :
    Real.log y≤y-1-(y-1)^2/8 := by
  let r := Real.sqrt y
  have hr : 0<r := Real.sqrt_pos.mpr hy
  have hrsq : r^2=y := Real.sq_sqrt hy.le
  have hrupper : r≤3/2 := by nlinarith
  have hlog := Real.log_le_sub_one_of_pos hr
  have hlogs : Real.log r=Real.log y/2 := Real.log_sqrt hy.le
  rw [hlogs] at hlog
  have hnonneg : 0≤(r-1)^2*(8-(r+1)^2) :=
    mul_nonneg (sq_nonneg _) (by nlinarith)
  have hsq : (y-1)^2≤8*(r-1)^2 := by nlinarith [sq_nonneg (r-1)]
  nlinarith

/-- Above two, the coordinate-product envelope is at most 2/e.
This follows directly from the exponential tangent bound. -/
theorem coordinate_exp_envelope_le_two_div_exp (y : ℝ) (hy : 2≤y) :
    y*Real.exp (1-y)≤2/Real.exp 1 := by
  have ht := Real.add_one_le_exp (y-2)
  have h : y≤2*Real.exp (y-2) := by linarith
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (1-y)).le
  apply hm.trans_eq
  rw [mul_assoc,← Real.exp_add]
  have he : y-2+(1-y)=-(1:ℝ) := by ring
  rw [he,Real.exp_neg]
  ring

theorem two_div_exp_one_lt_three_quarters : (2:ℝ)/Real.exp 1<3/4 := by
  apply (div_lt_iff₀ (Real.exp_pos 1)).mpr
  have h := Real.exp_one_gt_d9
  linarith

/-- A product exceeding three quarters forces every scaled row into (0,2),
including when nonnegativity, rather than strict positivity, was assumed. -/
theorem product_large_coordinate_bounds {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0≤y i) (hs : ∑ i,y i=d) (hp : 3/4<∏ i,y i) (i : Fin d) :
    0<y i ∧ y i<2 := by
  have hypos : 0<y i := by
    by_contra hn
    have hz : y i=0 := le_antisymm (le_of_not_gt hn) (hy i)
    have hpz : (∏ j,y j)=0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
    rw [hpz] at hp
    norm_num at hp
  refine ⟨hypos,?_⟩
  by_contra hn
  have hupper := (product_le_coordinate_mul_exp hy hs i).trans
    (coordinate_exp_envelope_le_two_div_exp (y i) (le_of_not_gt hn))
  exact (not_lt_of_ge hupper) (two_div_exp_one_lt_three_quarters.trans hp)

theorem product_large_sq_deviation_le_log {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0≤y i) (hs : ∑ i,y i=d) (hp : 3/4<∏ i,y i) :
    (∑ i,(y i-1)^2)≤-8*Real.log (∏ i,y i) := by
  have hi (i : Fin d) := product_large_coordinate_bounds y hy hs hp i
  have h := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) =>
    log_le_sub_one_sub_sq_eighth (y i) (hi i).1 (hi i).2.le)
  have hlogs : (∑ i,Real.log (y i))=Real.log (∏ i,y i) :=
    (Real.log_prod (fun i _ => (hi i).1.ne')).symm
  have hsum : (∑ i,(y i-1))=0 := by
    simp only [Finset.sum_sub_distrib,hs,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      nsmul_eq_mul,mul_one,sub_self]
  rw [hlogs,Finset.sum_sub_distrib,hsum,← Finset.sum_div] at h
  linarith

/-- Quantitative product-deficit concentration, with its original deficit
denominator retained. The dimension does not appear in the right side. -/
theorem product_deficit_sq_deviation {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0≤y i) (hs : ∑ i,y i=d) (b : ℝ) (hb : b<1/4)
    (hp : 1-b≤∏ i,y i) :
    (∑ i,(y i-1)^2)≤8*b/(1-b) := by
  have hprod : 3/4<∏ i,y i := lt_of_lt_of_le (by linarith) hp
  have hbpos : 0<1-b := by linarith
  have hl := Real.log_le_log hbpos hp
  have he := neg_log_one_sub_le_div b (by linarith)
  have hv := product_large_sq_deviation_le_log y hy hs hprod
  rw [mul_div_assoc]
  linarith

theorem product_deficit_sq_deviation_small {d : ℕ} (y : Fin d → ℝ)
    (hy : ∀ i,0≤y i) (hs : ∑ i,y i=d) (b : ℝ) (hb : b≤1/16384)
    (hp : 1-b≤∏ i,y i) :
    (∑ i,(y i-1)^2)<1/1024 := by
  have h := product_deficit_sq_deviation y hy hs b (by linarith) hp
  have hden : 0<1-b := by linarith
  have hbound : 8*b/(1-b)≤8/16383 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  exact (h.trans hbound).trans_lt (by norm_num)

/-- Concentration is derived from the actual full-probability contender
relation; no stationary condition or gauge is assumed. -/
theorem endpoint_contender_scaled_row_sq_small {m n : ℕ} (hm : 2≤m) (hmn : m≤n)
    {P : Board m n} (hP : IsProbability P)
    (hcont : uniformSeparationValue m n m≤separationProbability P m)
    (hb : distinctUniformProbability n m≤1/16384) :
    (∑ i,((m:ℝ)*rowSum P i-1)^2)<1/1024 := by
  have hs : (∑ i,(m:ℝ)*rowSum P i)=m := by
    rw [← Finset.mul_sum]
    change (m:ℝ)*totalMass P=m
    rw [hP.2,mul_one]
  have hp : 1-distinctUniformProbability n m≤∏ i,(m:ℝ)*rowSum P i := by
    rw [← endpointRowProduct_eq_product]
    exact endpoint_contender_rowProduct_lower hm hmn hP hcont
  exact product_deficit_sq_deviation_small (fun i => (m:ℝ)*rowSum P i)
    (fun i => mul_nonneg (Nat.cast_nonneg _) (rowSum_nonneg hP.1 i)) hs
    (distinctUniformProbability n m) hb hp

end DittertRybin
