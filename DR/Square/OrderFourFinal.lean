import DR.Square.OrderFourPolynomialIdentity
import DR.Square.OrderFourPolynomialBound
import DR.Square.Normalization

/-!
# Dittert's inequality at order four, including exact equality

The rational sextic identity, complete multiplier and monomial coverage,
and positive semidefinite seed certificates are all discharged in Lean.
The proof covers the full closed probability simplex and its equivalent
nonnegative mass-four Dittert normalization.
-/

namespace DittertRybin

open Certificates
open scoped BigOperators

theorem orderFour_probability_bound (P : Board 4 4) (hP : IsProbability P) :
    separationProbability P 4 ≤ (183/1024:ℝ) := by
  have hx : ∀ i, 0 ≤ orderFourFlat P i := fun i => hP.1 _ _
  have h := orderFourCertificatePolynomial_nonneg (orderFourFlat P) hx
  rw [← orderFourSextic_certificate_identity, orderFourSexticGapPolynomial_probability P hP] at h
  linarith

theorem orderFour_probability_equality (P : Board 4 4) (hP : IsProbability P) :
    separationProbability P 4 = (183/1024:ℝ) ↔ P = uniformBoard 4 4 := by
  constructor
  · intro heq
    have hx : ∀ i, 0 ≤ orderFourFlat P i := fun i => hP.1 _ _
    have hsum : ∑ i, orderFourFlat P i = 1 := (orderFour_sum_flat P).trans hP.2
    have hz : rationalEval (orderFourFlat P) orderFourCertificatePolynomial = 0 := by
      rw [← orderFourSextic_certificate_identity,
        orderFourSexticGapPolynomial_probability P hP, heq, sub_self]
    have hr := orderFourCertificatePolynomial_zero_rigid (orderFourFlat P) hx hsum hz
    funext i j
    have h := hr (orderFourCell (i,j))
    simp only [orderFourFlat, Equiv.symm_apply_apply] at h
    norm_num [uniformBoard]
    exact h
  · rintro rfl
    exact orderFour_uniform_value

theorem uniformMaximizer_four_four_four : UniformMaximizer 4 4 4 := by
  intro P hP
  have hu : uniformSeparationValue 4 4 4 = (183/1024:ℝ) := by
    norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]
  rw [hu]
  exact ⟨orderFour_probability_bound P hP, orderFour_probability_equality P hP⟩

theorem dittert_order_four : DittertMaximizer 4 :=
  (uniformMaximizer_iff_dittertMaximizer (by decide : 0 < 4)).mp uniformMaximizer_four_four_four

end DittertRybin
