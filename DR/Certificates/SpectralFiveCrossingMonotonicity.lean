import DR.Certificates.SpectralFiveTwoBlockBounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The two complementary block floors decrease up to the certified crossing cap. -/

namespace DittertRybin.Certificates.SpectralFiveTwoBlocks
noncomputable section
open Set

def smallBlockFloorAt (u v w : ℝ) : ℝ :=
  (1-((w-u-v)/2)/(79/100))/(1+u/3)^3 +
    (1-v/3-(w+u+v)/2)/(1-v/3)^4 - (3/2)*(1+(v-u-w)/4)^2

def largeBlockFloorAt (u v w : ℝ) : ℝ :=
  (1-u/2-(w+u+v)/2)/(1-u/2)^3 +
    (1-((w-u-v)/2)/(79/100))/(1+v/2)^2 - (16/9)*(1+(u-v-w)/6)^3

theorem smallBlockFloorAt_hasDerivAt (u v w : ℝ) :
    HasDerivAt (smallBlockFloorAt u v)
      (-1/((79/50)*(1+u/3)^3)-1/(2*(1-v/3)^4)+(3/4)*(1+(v-u-w)/4)) w := by
  have h := (((((((hasDerivAt_id w).sub_const u).sub_const v).div_const 2).div_const (79/100)).const_sub 1).div_const ((1+u/3)^3)).add
    ((((((hasDerivAt_id w).add_const u).add_const v).div_const 2).const_sub (1-v/3)).div_const ((1-v/3)^4))
  have hh := h.sub ((((((hasDerivAt_id w).const_sub (v-u)).div_const 4).const_add 1).pow 2).const_mul (3/2))
  simp only [id_eq] at hh
  convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv, mul_inv_rev]; ring)

theorem largeBlockFloorAt_hasDerivAt (u v w : ℝ) :
    HasDerivAt (largeBlockFloorAt u v)
      (-1/(2*(1-u/2)^3)-1/((79/50)*(1+v/2)^2)+(8/9)*(1+(u-v-w)/6)^2) w := by
  have h := ((((((hasDerivAt_id w).add_const u).add_const v).div_const 2).const_sub (1-u/2)).div_const ((1-u/2)^3)).add
    (((((((hasDerivAt_id w).sub_const u).sub_const v).div_const 2).div_const (79/100)).const_sub 1).div_const ((1+v/2)^2))
  have hh := h.sub ((((((hasDerivAt_id w).const_sub (u-v)).div_const 6).const_add 1).pow 3).const_mul (16/9))
  simp only [id_eq] at hh
  convert hh using 1 <;> first | rfl | (simp only [div_eq_mul_inv, mul_inv_rev]; ring)

theorem smallBlockFloorAt_derivative_neg {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huvw : u+v ≤ w) (hw : w ≤ 13/50) :
    -1/((79/50)*(1+u/3)^3)-1/(2*(1-v/3)^4)+(3/4)*(1+(v-u-w)/4) < 0 := by
  have hr : 0 < 1+u/3 := by linarith
  have hs : 0 < 1-v/3 := by linarith
  have hrpow : (1+u/3)^3 ≤ (163/150 : ℝ)^3 :=
    pow_le_pow_left₀ hr.le (by linarith) 3
  have hspow : (1-v/3)^4 ≤ (1:ℝ)^4 := pow_le_pow_left₀ hs.le (by linarith) 4
  have hir : (1/3 : ℝ) ≤ 1/((79/50)*(1+u/3)^3) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have his : (1/2 : ℝ) ≤ 1/(2*(1-v/3)^4) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  simp only [neg_div]
  linarith

theorem largeBlockFloorAt_derivative_neg {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huvw : u+v ≤ w) (hw : w ≤ 13/50) :
    -1/(2*(1-u/2)^3)-1/((79/50)*(1+v/2)^2)+(8/9)*(1+(u-v-w)/6)^2 < 0 := by
  have ha : 0 < 1-u/2 := by linarith
  have hb : 0 < 1+v/2 := by linarith
  have hapow : (1-u/2)^3 ≤ (1:ℝ)^3 := pow_le_pow_left₀ ha.le (by linarith) 3
  have hbpow : (1+v/2)^2 ≤ (113/100:ℝ)^2 :=
    pow_le_pow_left₀ hb.le (by linarith) 2
  have hia : (1/2:ℝ) ≤ 1/(2*(1-u/2)^3) := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hib : (5/12:ℝ) ≤ 1/((79/50)*(1+v/2)^2) := by
    have hh : 1/(12/5:ℝ) ≤ 1/((79/50)*(1+v/2)^2) := by
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    norm_num at hh ⊢
    exact hh
  have hm0 : 0 ≤ 1+(u-v-w)/6 := by linarith
  have hm1 : 1+(u-v-w)/6 ≤ 1 := by linarith
  have hmpow : (1+(u-v-w)/6)^2 ≤ (1:ℝ)^2 := pow_le_pow_left₀ hm0 hm1 2
  simp only [neg_div]
  linarith

theorem smallBlockFloor_le_actual {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huvw : u+v ≤ w) (hw : w ≤ 13/50) :
    smallBlockFloor u v ≤ smallBlockFloorAt u v w := by
  have hm : AntitoneOn (smallBlockFloorAt u v) (Icc (u+v) (13/50)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · intro z _; exact (smallBlockFloorAt_hasDerivAt u v z).continuousAt.continuousWithinAt
    · intro z _; exact (smallBlockFloorAt_hasDerivAt u v z).hasDerivWithinAt
    · intro z hz
      exact (smallBlockFloorAt_derivative_neg hu hv (interior_subset hz).1 (interior_subset hz).2).le
  exact hm ⟨huvw,hw⟩ ⟨huvw.trans hw,le_rfl⟩ hw

theorem largeBlockFloor_le_actual {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huvw : u+v ≤ w) (hw : w ≤ 13/50) :
    largeBlockFloor u v ≤ largeBlockFloorAt u v w := by
  have hm : AntitoneOn (largeBlockFloorAt u v) (Icc (u+v) (13/50)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
    · intro z _; exact (largeBlockFloorAt_hasDerivAt u v z).continuousAt.continuousWithinAt
    · intro z _; exact (largeBlockFloorAt_hasDerivAt u v z).hasDerivWithinAt
    · intro z hz
      exact (largeBlockFloorAt_derivative_neg hu hv (interior_subset hz).1 (interior_subset hz).2).le
  exact hm ⟨huvw,hw⟩ ⟨huvw.trans hw,le_rfl⟩ hw

end
end DittertRybin.Certificates.SpectralFiveTwoBlocks
