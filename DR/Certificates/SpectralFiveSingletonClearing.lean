import DR.Certificates.SpectralFiveDerivative
import DR.Certificates.SpectralFiveGuards

/-! Exact denominator clearing for the literal order-five singleton minor bound. -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section

/-- The distinguished entry, in minimum-row/maximum-column marginal coordinates. -/
def singletonEntry (a b w : ℝ) : ℝ := (a + b - w) / 2

/-- The actual order-four minor lower bound, with its exact mass normalization. -/
def singletonMinorFloor (a b L delta w : ℝ) : ℝ :=
  (3 * a - b - w) / (2 * a ^ 2) + (2 * L - w - a + b) / (2 * L * b) - delta -
    (61 / 32) * ((10 - a - b - w) / 8) ^ 4

/-- The explicit cleared numerator; n/V is the marginal-product deficit. -/
def singletonClearedNumerator (a b L d U n V : ℝ) : ℝ :=
  (2*d*(a+b)-U) *
    (V*16384*d^3 * ((2*d*(3*a-b)-U)*L*b + (2*d*(2*L-a+b)-U)*a^2) -
      n*(16*d)^4*a^2*L*b - (61/32)*(2*d*(10-a-b)-U)^4*a^2*L*b*V) -
  4*d*((24/625)*V-n)*(16*d)^4*a^2*L*b

/-- The full denominator is recorded explicitly rather than suppressed in a sign check. -/
def singletonClearedDenominator (a b L d V : ℝ) : ℝ :=
  4*d*(16*d)^4*a^2*L*b*V

theorem singleton_cleared_identity (a b L d U n V : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hL : L ≠ 0) (hd : d ≠ 0) (hV : V ≠ 0) :
    singletonClearedNumerator a b L d U n V = singletonClearedDenominator a b L d V *
      (singletonEntry a b (U/(2*d)) * singletonMinorFloor a b L (n/V) (U/(2*d)) -
        ((24/625)-n/V)) := by
  unfold singletonClearedNumerator singletonClearedDenominator singletonEntry singletonMinorFloor
  field_simp [ha, hb, hL, hd, hV]
  ring

theorem singleton_cleared_denominator_pos {a b L d V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (hd : 0 < d) (hV : 0 < V) :
    0 < singletonClearedDenominator a b L d V := by
  unfold singletonClearedDenominator
  positivity

/-- Positivity of the proved numerator transfers to the literal entry-times-minor gap. -/
theorem singleton_gap_of_cleared_positive {a b L d U n V : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 0 < L) (hd : 0 < d) (hV : 0 < V)
    (hN : 0 < singletonClearedNumerator a b L d U n V) :
    24/625-n/V < singletonEntry a b (U/(2*d)) * singletonMinorFloor a b L (n/V) (U/(2*d)) := by
  rw [singleton_cleared_identity a b L d U n V ha.ne' hb.ne' hL.ne' hd.ne' hV.ne'] at hN
  have hD := singleton_cleared_denominator_pos ha hb hL hd hV
  have hg := pos_of_mul_pos_right hN hD.le
  linarith

end
end DittertRybin.Certificates.SpectralFiveSingleton
