import DR.Certificates.SpectralFiveSingletonIdentity
import DR.Certificates.SpectralFiveSingletonDataPositive
import DR.Certificates.BernsteinPositiveBlend
import DR.Certificates.SpectralFiveSingletonBounds

/-! The complete closed-box singleton certificate, tied to the literal numerator. -/
namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section
open scoped BigOperators
open MvPolynomial

theorem singletonBlockPolynomial_eval (t x y : ℝ) (i : Fin 8) (j : Fin 7) :
    rationalEval ![t,x,y] (singletonBlockPolynomial i j) =
      rationalEval (fun _ : Fin 1 => t) (powerPolynomial (blockPowerCoefficients i j)) := by
  simp [rationalEval, singletonBlockPolynomial, powerPolynomial]

theorem singletonPolynomial_pos (t x y : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9/20)
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < rationalEval ![t,x,y] singletonPolynomial := by
  have h := congrArg (rationalEval ![t,x,y]) scaledSingletonPolynomial_eq_bernstein
  have he (i : Fin 8) (j : Fin 7) := singletonBlockPolynomial_eval t x y i j
  have hp := bernstein_two_positive_blend
    (fun i j => rationalEval (fun _ : Fin 1 => t)
      (powerPolynomial (blockPowerCoefficients i j)))
    (blockPowerCoefficients_pos t ht ht1) x y hx hx1 hy hy1
  have hb :
      rationalEval ![t,x,y] scaledSingletonPolynomial =
        ∑ i : Fin 8, ∑ j : Fin 7,
          rationalEval (fun _ : Fin 1 => t) (powerPolynomial (blockPowerCoefficients i j)) *
            bernsteinWeight 7 i x * bernsteinWeight 6 j y := by
    rw [h]
    simp only [rationalEval, eval₂_sum, eval₂_mul, eval₂_pow, eval₂_C,
      eval₂_sub, eval₂_one, eval₂_X]
    simp only [rationalEval] at he
    simp_rw [he]
    simp [bernsteinWeight]
  rw [← hb] at hp
  have hs : rationalEval ![t,x,y] scaledSingletonPolynomial =
      (singletonScale : ℝ) * rationalEval ![t,x,y] singletonPolynomial := by
    simp [rationalEval, scaledSingletonPolynomial]
  rw [hs] at hp
  have hscale : 0 < (singletonScale : ℝ) := by exact_mod_cast singletonScale_pos
  exact (mul_pos_iff_of_pos_left hscale).mp hp

/-- The proved certificate implies the actual normalized singleton gap on every box face. -/
theorem singleton_normalized_gap_proved {t x y : ℝ}
    (ht : 0 ≤ t) (ht1 : t ≤ 9/20) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    24/625-t^2/(5+t^2) <
      singletonEntry (1-(23/50)*t*x) (1+(1/2)*t*y) (SpectralFiveGuards.crossingBound t) *
      singletonMinorFloor (1-(23/50)*t*x) (1+(1/2)*t*y) (1-(23/50)*t)
        (t^2/(5+t^2)) (SpectralFiveGuards.crossingBound t) :=
  singleton_normalized_gap ht ht1 hx hx1 hy hy1
    (singletonPolynomial_pos t x y ht ht1 hx hx1 hy hy1)

end
end DittertRybin.Certificates.SpectralFiveSingleton
