import DR.Certificates.SpectralFiveSingletonClearing
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The order-four minor floor decreases with the actual crossing, on its closed domain. -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open Set

theorem singletonMinorFloor_hasDerivAt (a b L delta w : ℝ) :
    HasDerivAt (singletonMinorFloor a b L delta)
      (-1/(2*a^2)-1/(2*L*b)+(61/64)*((10-a-b-w)/8)^3) w := by
  have h := (((((hasDerivAt_id w).const_sub (3*a-b)).div_const (2*a^2)).add
    ((((hasDerivAt_id w).const_sub (2*L)).sub_const a).add_const b |>.div_const (2*L*b))).sub_const delta).sub
      (((((hasDerivAt_id w).const_sub (10-a-b)).div_const 8).pow 4).const_mul (61/32))
  simp only [id_eq] at h
  convert h using 1 <;> first | rfl | ring

theorem singletonMinorFloor_antitone (a b L delta : ℝ)
    (ha : 793/1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49/40)
    (hL : 0 < L) (hLa : L ≤ a) :
    AntitoneOn (singletonMinorFloor a b L delta) (Icc 0 (13/50)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (13/50))
  · intro w _
    exact (singletonMinorFloor_hasDerivAt a b L delta w).continuousAt.continuousWithinAt
  · intro w _
    exact (singletonMinorFloor_hasDerivAt a b L delta w).hasDerivWithinAt
  · intro w hw
    exact (SpectralFiveDerivative.singleton_minor_derivative_neg a b L w ha ha1 hb hb1 hL hLa
      (interior_subset hw).1 (interior_subset hw).2).le

/-- A strict endpoint gap remains strict for any smaller nonnegative crossing. -/
theorem singleton_gap_of_crossing_le {a b L delta w W p : ℝ}
    (ha : 793/1000 ≤ a) (ha1 : a ≤ 1) (hb : 1 ≤ b) (hb1 : b ≤ 49/40)
    (hL : 0 < L) (hLa : L ≤ a) (hw : 0 ≤ w) (hwW : w ≤ W) (hW : W ≤ 13/50)
    (hp : 0 ≤ p)
    (hgap : p < singletonEntry a b W * singletonMinorFloor a b L delta W) :
    p < singletonEntry a b w * singletonMinorFloor a b L delta w := by
  have he : 0 < singletonEntry a b W := by unfold singletonEntry; linarith
  have hm : 0 < singletonMinorFloor a b L delta W :=
    pos_of_mul_pos_right (lt_of_le_of_lt hp hgap) he.le
  have hminor := singletonMinorFloor_antitone a b L delta ha ha1 hb hb1 hL hLa
    ⟨hw, hwW.trans hW⟩ ⟨hw.trans hwW, hW⟩ hwW
  have hentry : singletonEntry a b W ≤ singletonEntry a b w := by
    unfold singletonEntry; linarith
  exact hgap.trans_le (mul_le_mul hentry hminor hm.le (he.le.trans hentry))

end
end DittertRybin.Certificates.SpectralFiveSingleton
