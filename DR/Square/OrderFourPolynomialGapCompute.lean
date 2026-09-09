import DR.Square.OrderFourPolynomialGapCoefficients
import DR.Square.OrderFourPolynomialQuarticSemantics

/-!
# Exact finite extraction formula for the actual sextic gap

All multiset cardinalities and the inclusive-OR row/column distinction occur
explicitly in this formula, which follows from the actual quartic theorem.
-/

namespace DittertRybin

open MvPolynomial
open scoped BigOperators

noncomputable def orderFourGapCoefficientCompute (s : Multiset (Fin 16)) : ℚ :=
  (183/1024:ℚ)*(if s.card = 6 then (s.toFinsupp.multinomial : ℚ) else 0) -
    ∑ i : Fin 16, if i ∈ s then ∑ j : Fin 16, if j ∈ s.erase i then
      (if ((s.erase i).erase j).card = 4 ∧ orderFourQuarticSuccess ((s.erase i).erase j)
        then (24:ℚ) else 0) else 0 else 0

theorem orderFourSexticGapPolynomial_coeff_compute (s : Multiset (Fin 16)) :
    coeff s.toFinsupp orderFourSexticGapPolynomial = orderFourGapCoefficientCompute s := by
  rw [orderFourSexticGapPolynomial_coeff]
  simp only [orderFourQuarticPolynomial_coeff_multiset, orderFourGapCoefficientCompute]

end DittertRybin
