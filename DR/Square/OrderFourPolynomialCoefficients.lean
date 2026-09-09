import DR.Square.OrderFourPolynomialCertificate

/-!
# Sparse coefficient extraction for the sextic certificate

Deleting the two quadratic cells leaves a four-cell multiplier. This gives
a sum over at most 16 squared cell choices, independently of the total
number of quartic monomials. Non-multiplier cardinalities are zero explicitly.
-/

namespace DittertRybin

open Certificates MvPolynomial
open scoped BigOperators

noncomputable def orderFourRawMatrix (s : Multiset (Fin 16)) :
    Matrix (Fin 16) (Fin 16) ℚ :=
  if hs : s.card = 4 then orderFourMultiplierMatrix (orderFourSortedMultiplier ⟨s,hs⟩)
  else 0

theorem orderFour_toFinsupp_degree (s : Multiset (Fin 16)) :
    s.toFinsupp.degree = s.card := by
  change s.toFinsupp.sum (fun _ => id) = s.card
  exact Multiset.toFinsupp_sum_eq s

theorem orderFourQuarticEntryPolynomial_coeff_multiset
    (s : Multiset (Fin 16)) (i j : Fin 16) :
    coeff s.toFinsupp (orderFourQuarticEntryPolynomial i j) = orderFourRawMatrix s i j := by
  classical
  by_cases hs : s.card = 4
  · simpa only [orderFourRawMatrix, dif_pos hs, orderFourExponent] using
      orderFourQuarticEntryPolynomial_coeff ⟨s,hs⟩ i j
  · rw [(orderFourQuarticEntryPolynomial_isHomogeneous i j).coeff_eq_zero
      (by simpa only [orderFour_toFinsupp_degree] using hs)]
    simp [orderFourRawMatrix, hs]

theorem orderFour_toFinsupp_cons (i : Fin 16) (s : Multiset (Fin 16)) :
    (i ::ₘ s).toFinsupp = Finsupp.single i 1 + s.toFinsupp := by
  rw [← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton]

theorem orderFour_coeff_X_mul_multiset (s : Multiset (Fin 16)) (i : Fin 16)
    (p : MvPolynomial (Fin 16) ℚ) :
    coeff s.toFinsupp (X i * p) =
      if i ∈ s then coeff (s.erase i).toFinsupp p else 0 := by
  classical
  by_cases hi : i ∈ s
  · rw [if_pos hi]
    have he := congrArg (fun t : Multiset (Fin 16) => t.toFinsupp) (Multiset.cons_erase hi)
    rw [orderFour_toFinsupp_cons] at he
    rw [← he, coeff_X_mul]
  · rw [if_neg hi, coeff_X_mul']
    simp [Multiset.toFinsupp_support, hi]

/-- The coefficient contributed by all choices of the two ordered quadratic cells. -/
noncomputable def orderFourCertificateCoefficient (s : Multiset (Fin 16)) : ℚ :=
  ∑ i : Fin 16, if i ∈ s then
    ∑ j : Fin 16, if j ∈ s.erase i then orderFourRawMatrix ((s.erase i).erase j) i j else 0
    else 0

theorem orderFourCertificatePolynomial_coeff (s : Multiset (Fin 16)) :
    coeff s.toFinsupp orderFourCertificatePolynomial = orderFourCertificateCoefficient s := by
  classical
  simp only [orderFourCertificatePolynomial, coeff_sum, orderFour_coeff_X_mul_multiset]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases his : i ∈ s
  · simp only [his, if_true, orderFourQuarticEntryPolynomial_coeff_multiset]
  · simp [his]

end DittertRybin
