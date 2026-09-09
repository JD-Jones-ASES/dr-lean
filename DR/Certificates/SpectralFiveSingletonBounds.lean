import DR.Certificates.SpectralFiveSingletonPolynomial
import DR.Certificates.SpectralFiveSingletonClearing

/-! The singleton polynomial evaluates to the original rational minor gap. -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open MvPolynomial

theorem eval_energy (t x y : ℝ) : rationalEval ![t,x,y] energyPolynomial =
    SpectralFiveGuards.energy t := by
  norm_num [rationalEval, energyPolynomial, heightPolynomial,
    SpectralFiveGuards.energy, SpectralFiveGuards.height]
  ring_nf
  simp

theorem eval_denominator (t x y : ℝ) : rationalEval ![t,x,y] denominatorPolynomial =
    SpectralFiveGuards.denominator t := by
  have he := eval_energy t x y
  unfold rationalEval at *
  norm_num [denominatorPolynomial, qPolynomial, SpectralFiveGuards.denominator,
    SpectralFiveGuards.domination, he]

theorem eval_crossing (t x y : ℝ) : rationalEval ![t,x,y] crossingPolynomial =
    SpectralFiveGuards.crossingNumerator t := by
  have he := eval_energy t x y
  unfold rationalEval at *
  norm_num [crossingPolynomial, qPolynomial, SpectralFiveGuards.crossingNumerator,
    SpectralFiveGuards.domination, he]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem eval_singletonPolynomial (t x y : ℝ) :
    rationalEval ![t,x,y] singletonPolynomial =
      singletonClearedNumerator (1-(23/50)*t*x) (1+(1/2)*t*y) (1-(23/50)*t)
        (SpectralFiveGuards.denominator t) (SpectralFiveGuards.crossingNumerator t)
        (t^2) (5+t^2) := by
  have hd := eval_denominator t x y
  have hU := eval_crossing t x y
  unfold rationalEval at *
  norm_num [singletonPolynomial, anPolynomial, enPolynomial, rnPolynomial, cnPolynomial,
    snPolynomial, commonPolynomial, uPolynomial, vPolynomial, lowerPolynomial, hd, hU,
    singletonClearedNumerator]
  dsimp
  ring

/-- Positive source-polynomial values imply the normalized literal singleton gap. -/
theorem singleton_normalized_gap {t x y : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 9/20) (_hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : 0 ≤ y) (_hy1 : y ≤ 1)
    (hP : 0 < rationalEval ![t,x,y] singletonPolynomial) :
    24/625-t^2/(5+t^2) <
      singletonEntry (1-(23/50)*t*x) (1+(1/2)*t*y) (SpectralFiveGuards.crossingBound t) *
      singletonMinorFloor (1-(23/50)*t*x) (1+(1/2)*t*y) (1-(23/50)*t)
        (t^2/(5+t^2)) (SpectralFiveGuards.crossingBound t) := by
  have htx : t*x ≤ t := by nlinarith
  have ha : 0 < 1-(23/50)*t*x := by nlinarith
  have hb : 0 < 1+(1/2)*t*y := by positivity
  have hL : 0 < 1-(23/50)*t := by linarith
  have hd := SpectralFiveGuards.denominator_pos t ht ht1
  have hV : 0 < 5+t^2 := by positivity
  rw [eval_singletonPolynomial] at hP
  exact singleton_gap_of_cleared_positive ha hb hL hd hV hP

end
end DittertRybin.Certificates.SpectralFiveSingleton
