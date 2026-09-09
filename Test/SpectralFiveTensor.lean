import DR.Certificates.SpectralFiveDerivative
import DR.Certificates.SpectralFiveTwoBlocks

namespace DittertRybin.Tests
open Certificates

-- The endpoint minimum in the exact derivative table is retained.
example : SpectralFiveDerivative.margin = (323125053 / 4194304000 : ℚ) := by rfl

#print axioms SpectralFiveDerivative.derivativePolynomial_pos
#print axioms SpectralFiveDerivative.singleton_minor_derivative_neg
#print axioms SpectralFiveTwoBlocks.xAbove_polynomial_pos
#print axioms SpectralFiveTwoBlocks.yAbove_polynomial_pos
#print axioms SpectralFiveTwoBlocks.sumBelow_polynomial_pos
#print axioms SpectralFiveTwoBlocks.productAbove_polynomial_pos
end DittertRybin.Tests
