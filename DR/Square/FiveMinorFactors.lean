import DR.Certificates.SpectralFiveCrossingMonotonicity
import DR.Certificates.SpectralFiveSingletonClearing
import Mathlib.Algebra.Order.Ring.Pow

/-! The four actual two-block product factors and the two singleton factors. -/

namespace DittertRybin
noncomputable section

def fiveSmallRowFactor (u v w : ℝ) : ℝ :=
  (1-((w-u-v)/2)/(79/100))/(1+u/3)^3
def fiveSmallColFactor (u v w : ℝ) : ℝ :=
  (1-v/3-(w+u+v)/2)/(1-v/3)^4
def fiveLargeRowFactor (u v w : ℝ) : ℝ :=
  (1-u/2-(w+u+v)/2)/(1-u/2)^3
def fiveLargeColFactor (u v w : ℝ) : ℝ :=
  (1-((w-u-v)/2)/(79/100))/(1+v/2)^2

theorem five_two_block_factor_bounds {u v w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huw : u+v ≤ w) (hw : w ≤ 13/50) :
    (0 < fiveSmallRowFactor u v w ∧ fiveSmallRowFactor u v w ≤ 1) ∧
    (0 < fiveSmallColFactor u v w ∧ fiveSmallColFactor u v w ≤ 1) ∧
    (0 < fiveLargeRowFactor u v w ∧ fiveLargeRowFactor u v w ≤ 1) ∧
    (0 < fiveLargeColFactor u v w ∧ fiveLargeColFactor u v w ≤ 1) := by
  have hr : 0 < 1+u/3 := by linarith
  have hs : 0 < 1-v/3 := by linarith
  have ha : 0 < 1-u/2 := by linarith
  have hb : 0 < 1+v/2 := by linarith
  have hnum : 0 < 1-((w-u-v)/2)/(79/100) := by linarith
  have hnum1 : 1-((w-u-v)/2)/(79/100) ≤ 1 := by linarith
  have hnumS : 0 < 1-v/3-(w+u+v)/2 := by linarith
  have hnumA : 0 < 1-u/2-(w+u+v)/2 := by linarith
  have hrpow : (1:ℝ)^3 ≤ (1+u/3)^3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hbpow : (1:ℝ)^2 ≤ (1+v/2)^2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hsBern : 1-4*(v/3) ≤ (1-v/3)^4 := by
    convert one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ -(v/3)) 4 using 1 <;> first | rfl | ring
  have haBern : 1-3*(u/2) ≤ (1-u/2)^3 := by
    convert one_add_mul_le_pow (by linarith : (-2:ℝ) ≤ -(u/2)) 3 using 1 <;> first | rfl | ring
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact div_pos hnum (pow_pos hr _)
  · apply (div_le_one (pow_pos hr 3)).mpr
    linarith
  · exact div_pos hnumS (pow_pos hs _)
  · apply (div_le_one (pow_pos hs 4)).mpr
    linarith
  · exact div_pos hnumA (pow_pos ha _)
  · apply (div_le_one (pow_pos ha 3)).mpr
    linarith
  · exact div_pos hnum (pow_pos hb _)
  · apply (div_le_one (pow_pos hb 2)).mpr
    linarith

def fiveSingletonRowFactor (a b w : ℝ) : ℝ := (3*a-b-w)/(2*a^2)
def fiveSingletonColFactor (a b L w : ℝ) : ℝ := (2*L-w-a+b)/(2*L*b)

theorem five_singleton_factor_bounds {a b L w : ℝ}
    (ha : 793/1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49/40)
    (hL : 793/1000 ≤ L) (hw : b-a ≤ w) (hw1 : w ≤ 13/50) :
    (0 < fiveSingletonRowFactor a b w ∧ fiveSingletonRowFactor a b w ≤ 1) ∧
    (0 < fiveSingletonColFactor a b L w ∧ fiveSingletonColFactor a b L w ≤ 1) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hL0 : 0 < L := by linarith
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · exact div_pos (by linarith) (by positivity)
  · apply (div_le_one (by positivity : 0 < 2*a^2)).mpr
    nlinarith [sq_nonneg (a-1)]
  · exact div_pos (by linarith) (by positivity)
  · apply (div_le_one (by positivity : 0 < 2*L*b)).mpr
    nlinarith [mul_nonneg hL0.le (sub_nonneg.mpr hb)]

end
end DittertRybin
