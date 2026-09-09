import DR.Certificates.SpectralFiveSingletonPositive

/-! Closed-face checks for the literal order-five singleton certificate. -/
namespace DittertRybin.Tests
open Certificates Certificates.SpectralFiveSingleton

-- The zero-deficit face is retained for arbitrary unit coordinates.
example (x y : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < rationalEval ![0,x,y] singletonPolynomial :=
  singletonPolynomial_pos 0 x y (by norm_num) (by norm_num) hx hx1 hy hy1

-- Both endpoints of both Bernstein axes are part of the proved closed box.
example : 0 < rationalEval ![(9/20 : ℝ),1,0] singletonPolynomial :=
  singletonPolynomial_pos (9/20) 1 0 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : 0 < rationalEval ![(9/20 : ℝ),0,1] singletonPolynomial :=
  singletonPolynomial_pos (9/20) 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- This check evaluates the original factored formula directly, independently
-- of the sparse table and its two-axis Bernstein conversion.
example : rationalEval ![(0 : ℝ),0,0] singletonPolynomial =
    4590382376849424248070319752 / 1818989403545856475830078125 := by
  norm_num [rationalEval, singletonPolynomial, enPolynomial, anPolynomial,
    snPolynomial, rnPolynomial, cnPolynomial, commonPolynomial,
    crossingPolynomial, denominatorPolynomial, energyPolynomial,
    heightPolynomial, qPolynomial, lowerPolynomial, uPolynomial, vPolynomial]

#print axioms scaledSingletonPolynomial_eq_power
#print axioms scaledSingletonPolynomial_eq_bernstein
#print axioms singletonPolynomial_pos
#print axioms singleton_normalized_gap_proved
end DittertRybin.Tests
