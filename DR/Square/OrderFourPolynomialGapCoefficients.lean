import DR.Square.OrderFourPolynomialCoefficients

/-!
# Sparse coefficients of the actual sextic probability gap

This is an algebraic extraction formula for the actual quartic. It retains
that quartic's coefficients explicitly; no certificate coefficient identity
is an input.
-/

namespace DittertRybin

open Certificates MvPolynomial
open scoped BigOperators

theorem orderFourTotalPolynomial_sq_mul (p : MvPolynomial (Fin 16) ℚ) :
    orderFourTotalPolynomial^2 * p = ∑ i : Fin 16, ∑ j : Fin 16, X i * (X j * p) := by
  simp only [orderFourTotalPolynomial, pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem orderFourTotalPolynomial_sq_mul_coeff (p : MvPolynomial (Fin 16) ℚ)
    (s : Multiset (Fin 16)) :
    coeff s.toFinsupp (orderFourTotalPolynomial^2 * p) =
      ∑ i : Fin 16, if i ∈ s then ∑ j : Fin 16, if j ∈ s.erase i then
        coeff ((s.erase i).erase j).toFinsupp p else 0 else 0 := by
  classical
  rw [orderFourTotalPolynomial_sq_mul]
  simp only [coeff_sum, orderFour_coeff_X_mul_multiset]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases his : i ∈ s <;> simp [his]

theorem orderFourTotalPolynomial_pow_coeff (s : Multiset (Fin 16)) (k : ℕ) :
    coeff s.toFinsupp (orderFourTotalPolynomial^k) =
      if s.card = k then (s.toFinsupp.multinomial : ℚ) else 0 := by
  rw [orderFourTotalPolynomial, coeff_sum_X_pow_of_fintype]
  have hs : s.toFinsupp.sum (fun _ m => m) = s.card := Multiset.toFinsupp_sum_eq s
  rw [hs]
  split_ifs <;> rfl

theorem orderFourSexticGapPolynomial_coeff (s : Multiset (Fin 16)) :
    coeff s.toFinsupp orderFourSexticGapPolynomial =
      (183/1024:ℚ)*(if s.card = 6 then (s.toFinsupp.multinomial : ℚ) else 0) -
      ∑ i : Fin 16, if i ∈ s then ∑ j : Fin 16, if j ∈ s.erase i then
        coeff ((s.erase i).erase j).toFinsupp orderFourQuarticPolynomial else 0 else 0 := by
  rw [orderFourSexticGapPolynomial, coeff_sub, coeff_C_mul,
    orderFourTotalPolynomial_pow_coeff, orderFourTotalPolynomial_sq_mul_coeff]

end DittertRybin
