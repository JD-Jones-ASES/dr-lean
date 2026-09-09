import DR.Square.OrderFourOrbitPSD
import DR.Square.OrderFourPolynomial
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# A polynomial assembled from the physical quadratic matrices

The outer sum runs over unordered four-cell multisets, with no multinomial
factor. This module establishes coefficient and evaluation interfaces before
any finite sextic identity is asserted.
-/

namespace DittertRybin

open Certificates MvPolynomial
open scoped BigOperators

noncomputable def orderFourExponent {n : ℕ} (s : Sym (Fin 16) n) : Fin 16 →₀ ℕ :=
  s.val.toFinsupp

theorem orderFourExponent_injective {n : ℕ} :
    Function.Injective (orderFourExponent (n := n)) := by
  intro s t h
  exact Subtype.ext (Multiset.toFinsupp.injective h)

theorem orderFourExponent_degree {n : ℕ} (s : Sym (Fin 16) n) :
    (orderFourExponent s).degree = n := by
  change s.val.toFinsupp.sum (fun _ => id) = n
  rw [Multiset.toFinsupp_sum_eq]
  exact s.property

noncomputable def orderFourQuarticEntryPolynomial (i j : Fin 16) : MvPolynomial (Fin 16) ℚ :=
  ∑ s : Sym (Fin 16) 4, monomial (orderFourExponent s)
    (orderFourMultiplierMatrix (orderFourSortedMultiplier s) i j)

noncomputable def orderFourCertificatePolynomial : MvPolynomial (Fin 16) ℚ :=
  ∑ i : Fin 16, ∑ j : Fin 16, X i * (X j * orderFourQuarticEntryPolynomial i j)

theorem orderFourQuarticEntryPolynomial_coeff (s : Sym (Fin 16) 4) (i j : Fin 16) :
    coeff (orderFourExponent s) (orderFourQuarticEntryPolynomial i j) =
      orderFourMultiplierMatrix (orderFourSortedMultiplier s) i j := by
  classical
  rw [orderFourQuarticEntryPolynomial, coeff_sum]
  rw [Fintype.sum_eq_single s]
  · simp
  · intro t hts
    have hne : orderFourExponent t ≠ orderFourExponent s :=
      fun h => hts (orderFourExponent_injective h)
    simp [coeff_monomial, hne]

theorem orderFourQuarticEntryPolynomial_isHomogeneous (i j : Fin 16) :
    (orderFourQuarticEntryPolynomial i j).IsHomogeneous 4 := by
  apply IsHomogeneous.sum
  intro s hs
  exact isHomogeneous_monomial
    (orderFourMultiplierMatrix (orderFourSortedMultiplier s) i j) (orderFourExponent_degree s)

theorem orderFourCertificatePolynomial_isHomogeneous :
    orderFourCertificatePolynomial.IsHomogeneous 6 := by
  apply IsHomogeneous.sum
  intro i hi
  apply IsHomogeneous.sum
  intro j hj
  exact (isHomogeneous_X ℚ i).mul
    ((isHomogeneous_X ℚ j).mul (orderFourQuarticEntryPolynomial_isHomogeneous i j))

/-- The value of one unordered multiplier monomial. -/
noncomputable def orderFourMultiplierValue (s : Sym (Fin 16) 4) (x : Fin 16 → ℝ) : ℝ :=
  (s.val.map x).prod

theorem orderFourExponent_eval (s : Sym (Fin 16) 4) (a : ℚ) (x : Fin 16 → ℝ) :
    rationalEval x (monomial (orderFourExponent s) a) =
      (a : ℝ) * orderFourMultiplierValue s x := by
  classical
  simp only [rationalEval, eval₂_monomial, orderFourExponent, orderFourMultiplierValue]
  congr 1
  rw [Finsupp.prod]
  simp only [Multiset.toFinsupp_support, Multiset.toFinsupp_apply]
  exact (Finset.prod_multiset_map_count s.val x).symm

theorem orderFourCertificatePolynomial_eval (x : Fin 16 → ℝ) :
    rationalEval x orderFourCertificatePolynomial =
      ∑ s : Sym (Fin 16) 4, orderFourMultiplierValue s x *
        quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
          (fun q : ℚ => (q : ℝ))) x := by
  simp only [orderFourCertificatePolynomial, rationalEval, eval₂_sum, eval₂_mul, eval₂_X]
  change (∑ i : Fin 16, ∑ j : Fin 16, x i * (x j *
    rationalEval x (orderFourQuarticEntryPolynomial i j))) = _
  simp only [orderFourQuarticEntryPolynomial, rationalEval, eval₂_sum]
  change (∑ i : Fin 16, ∑ j : Fin 16, x i * (x j *
    ∑ s : Sym (Fin 16) 4, rationalEval x (monomial (orderFourExponent s)
      (orderFourMultiplierMatrix (orderFourSortedMultiplier s) i j)))) = _
  simp only [orderFourExponent_eval, Finset.mul_sum, quadraticValue, Matrix.map_apply]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin 16)))
    (t := (Finset.univ : Finset (Sym (Fin 16) 4)))]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end DittertRybin
