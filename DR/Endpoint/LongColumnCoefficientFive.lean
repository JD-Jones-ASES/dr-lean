import DR.Endpoint.EndpointCoefficient
import DR.Endpoint.LeadingUniform
import DR.Endpoint.ColumnDeletionLower
import DR.Endpoint.LongColumnParameters

/-! The actual elementary coefficient at a long-column retained board,
using a linear collision bound after normalization. This replaces the
exponential2^k loss and permits every m>=5. -/
namespace DittertRybin
open scoped BigOperators

theorem endpoint_elementarySymmetric_scale {d : ℕ} (x : Fin d → ℝ) (c : ℝ) (k : ℕ) :
    elementarySymmetric (fun i => c*x i) k=c^k*elementarySymmetric x k := by
  unfold elementarySymmetric
  simp_rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.mul_sum]

theorem endpoint_factorial_half_coefficient_guard {m : ℕ} (hm : 5≤m) :
    8*(m:ℝ)^2*((m-2).factorial:ℝ)≤(m:ℝ)^m := by
  have hmR : (5:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  have ha := endpointLeading_alpha_le_five hm
  have hal : dittertConstant m≤1/16 := ha.trans (by norm_num)
  rw [dittertConstant,div_le_iff₀ (pow_pos hm0 m)] at hal
  have hfact := endpoint_leading_factorial_two (by omega : 2≤m)
  have hk : 0≤((m-2).factorial:ℝ) := Nat.cast_nonneg _
  have hcomp : 8*(m:ℝ)^2≤16*(m:ℝ)*((m:ℝ)-1) := by nlinarith only [hmR]
  have hmul := mul_le_mul_of_nonneg_right hcomp hk
  nlinarith only [hal,hfact,hmul]

theorem longColumn_five_coefficient_lower {m n : ℕ} (hm : 5≤m)
    (hn : 10000*m^2≤n) (P : Board m n) (hP : ∀ i j,0≤P i j)
    (hh : (3/4:ℝ)<totalMass P) (hc : ∀ j,colSum P j≤25/(n:ℝ)) :
    (totalMass P)^(m-2)/(2*((m-2).factorial:ℝ))≤averagingCoefficient P (m-2) := by
  let h := totalMass P
  let C := 25/((n:ℝ)*h)
  let k := m-2
  have hmR : (5:ℝ)≤m := by exact_mod_cast hm
  have hnR : (10000:ℝ)*(m:ℝ)^2≤n := by exact_mod_cast hn
  have hn0 : (0:ℝ)<n := by nlinarith
  have hh0 : 0<h := by dsimp [h]; linarith
  have hC : 0≤C := by dsimp [C]; positivity
  have hnorm := normalizeBoard_isProbability hP hh0
  have hcol (j) : colSum (normalizeBoard P) j≤C := by
    rw [colSum_normalizeBoard]
    have hi := div_le_div_of_nonneg_right (hc j) hh0.le
    simpa only [div_div,C,h,mul_comm] using hi
  have hsum : (∑ j,colSum (normalizeBoard P) j)=1 :=
    (totalMass_eq_sum_colSum (normalizeBoard P)).symm.trans hnorm.2
  have hb := endpointColumnLossFactor_bounds (by omega : 3≤m)
  have hNmass := mul_le_mul_of_nonneg_left hh.le hn0.le
  have hsmall : endpointColumnLossFactor m*C≤1/2 := by
    dsimp [C]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (mul_pos hn0 hh0)).mpr
    change (n:ℝ)*(3/4)≤(n:ℝ)*h at hNmass
    nlinarith only [hb.2,hNmass,hnR,sq_nonneg (m:ℝ)]
  have hE := endpoint_elementary_lower_two_lost (k:=k) (colSum (normalizeBoard P))
    (colSum_nonneg hnorm.1) hC hcol hsum.le (by rw [hsum]; linarith only [hC])
  change 1-endpointColumnLossFactor m*C≤(k.factorial:ℝ)*elementarySymmetric (colSum (normalizeBoard P)) k at hE
  have hhalf : (1/2:ℝ)≤(k.factorial:ℝ)*elementarySymmetric (colSum (normalizeBoard P)) k := by
    linarith only [hE,hsmall]
  have hscaled := mul_le_mul_of_nonneg_left hhalf (pow_nonneg hh0.le k)
  have hcolId : (fun j => h*colSum (normalizeBoard P) j)=colSum P := by
    funext j
    rw [colSum_normalizeBoard]
    dsimp [h]
    exact mul_div_cancel₀ _ hh0.ne'
  have hEid : h^k*elementarySymmetric (colSum (normalizeBoard P)) k=averagingCoefficient P k := by
    rw [← endpoint_elementarySymmetric_scale,hcolId]
    rfl
  have hf : 0<(k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  change h^k/(2*(k.factorial:ℝ))≤averagingCoefficient P k
  apply (div_le_iff₀ (by positivity : 0<2*(k.factorial:ℝ))).mpr
  nlinarith only [hscaled,hEid]

theorem longColumn_five_coefficient_ratio {m n : ℕ} (hm : 5≤m)
    (hn : 10000*m^2≤n) (P : Board m n) (hP : ∀ i j,0≤P i j)
    (hr : ∀ i,0<rowSum P i) (hh : (3/4:ℝ)<totalMass P)
    (hp : 0<rowAvoidance (normalizeRows P)) (hc : ∀ j,colSum P j≤25/(n:ℝ)) :
    4*(m:ℝ)^2≤averagingCoefficient P (m-2)/
      (((∏ i,rowSum P i)/(totalMass P)^2)*rowAvoidance (normalizeRows P)) := by
  let h := totalMass P
  let G := (∏ i,rowSum P i)/h^2
  let p := rowAvoidance (normalizeRows P)
  let k := m-2
  have hh0 : 0<h := by dsimp [h]; linarith
  have hm0 : (0:ℝ)<m := by exact_mod_cast (by omega : 0<m)
  have hG : 0<G := div_pos (Finset.prod_pos (fun i _ => hr i)) (sq_pos_of_pos hh0)
  have hp1 : p≤1 := rowAvoidance_le_one (normalizeRows P)
    (normalizeRows_nonneg P hP) (normalizeRows_rowSum P (fun i => (hr i).ne'))
  have hGp : G*p≤h^k/(m:ℝ)^m :=
    (mul_le_of_le_one_right hG.le hp1).trans (endpoint_row_product_scale_le (by omega) P hP hh0)
  have hE := longColumn_five_coefficient_lower hm hn P hP hh hc
  have hguard := endpoint_factorial_half_coefficient_guard hm
  have hf : 0<(k.factorial:ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hscale : 4*(m:ℝ)^2*(h^k/(m:ℝ)^m)≤h^k/(2*(k.factorial:ℝ)) := by
    apply (le_div_iff₀ (by positivity : 0<2*(k.factorial:ℝ))).mpr
    have ht := mul_le_mul_of_nonneg_right hguard
      (div_nonneg (pow_nonneg hh0.le k) (pow_nonneg hm0.le m))
    have he : (m:ℝ)^m*(h^k/(m:ℝ)^m)=h^k := mul_div_cancel₀ _ (pow_ne_zero _ hm0.ne')
    rw [he] at ht
    convert ht using 1
    ring
  apply (le_div_iff₀ (mul_pos hG hp)).mpr
  exact (mul_le_mul_of_nonneg_left hGp (by positivity)).trans (hscale.trans hE)

end DittertRybin
