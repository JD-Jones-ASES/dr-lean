import DR.Square.OrderFourPolynomialSexticExt
import DR.Square.OrderFourPolynomialSexticCheck
import DR.Square.OrderFourPolynomialGapCheck

/-!
# The exact degree-six order-four certificate identity

The representative equalities on both sides are independently checked from
their proved extraction formulas. Complete physical orbit coverage then
identifies every degree-six coefficient.
-/

namespace DittertRybin

open MvPolynomial

theorem orderFourSextic_certificate_identity :
    orderFourSexticGapPolynomial = orderFourCertificatePolynomial := by
  apply orderFourSextic_polynomial_ext _ _ orderFourSexticGapPolynomial_isHomogeneous
    orderFourCertificatePolynomial_isHomogeneous orderFourSexticGapPolynomial_rename
    orderFourCertificatePolynomial_rename
  intro s
  rw [orderFourSexticGapPolynomial_coeff_compute, orderFourCertificatePolynomial_coeff,
    orderFourGapCoefficient_eq_expected, orderFourCertificateCoefficient_seed]

end DittertRybin
