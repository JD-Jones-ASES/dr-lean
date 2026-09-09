import DR.Square.OrderFourPolynomialCertificate

/-!
# Nonnegativity and rigidity of the full sextic certificate

Every multiplier weight is nonnegative on the closed orthant. One repeated
positive cell suffices for rigidity, so no strictly positive board hypothesis
or limiting argument is needed at a boundary face.
-/

namespace DittertRybin

open Certificates
open scoped BigOperators

theorem orderFourMultiplierValue_nonneg (s : Sym (Fin 16) 4) (x : Fin 16 → ℝ)
    (hx : ∀ i, 0 ≤ x i) : 0 ≤ orderFourMultiplierValue s x := by
  unfold orderFourMultiplierValue
  apply Multiset.prod_nonneg
  intro y hy
  obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hy
  exact hx i

theorem orderFour_centered_nonneg (x : Fin 16 → ℝ) :
    0 ≤ (∑ i, x i^2)-(∑ i, x i)^2/16 := by
  rw [← sum_centered_sixteen]
  exact Finset.sum_nonneg fun i hi => sq_nonneg _

theorem orderFourSortedMultiplier_quadratic_nonneg (s : Sym (Fin 16) 4) (x : Fin 16 → ℝ) :
    0 ≤ quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
      (fun q : ℚ => (q : ℝ))) x :=
  (mul_nonneg (by norm_num) (orderFour_centered_nonneg x)).trans
    (orderFourSortedMultiplier_lower s x)

theorem orderFourCertificatePolynomial_nonneg (x : Fin 16 → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ rationalEval x orderFourCertificatePolynomial := by
  rw [orderFourCertificatePolynomial_eval]
  exact Finset.sum_nonneg fun s hs => mul_nonneg (orderFourMultiplierValue_nonneg s x hx)
    (orderFourSortedMultiplier_quadratic_nonneg s x)

theorem orderFourCertificatePolynomial_zero_rigid (x : Fin 16 → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hsum : ∑ i, x i = 1)
    (hz : rationalEval x orderFourCertificatePolynomial = 0) :
    ∀ i, x i = (1/16:ℝ) := by
  have hpos : ∃ a, 0 < x a := by
    by_contra hn
    push Not at hn
    have hall : ∀ a, x a = 0 := fun a => le_antisymm (hn a) (hx a)
    simp only [hall, Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨a,ha⟩ := hpos
  let s : Sym (Fin 16) 4 := Sym.replicate 4 a
  have hweight : 0 < orderFourMultiplierValue s x := by
    simpa [s, orderFourMultiplierValue, Sym.coe_replicate, pow_succ, pow_zero, mul_assoc] using pow_pos ha 4
  have hterm : orderFourMultiplierValue s x *
      quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
        (fun q : ℚ => (q : ℝ))) x ≤ 0 := by
    rw [orderFourCertificatePolynomial_eval] at hz
    have h := Finset.single_le_sum
      (s := (Finset.univ : Finset (Sym (Fin 16) 4)))
      (fun t ht => mul_nonneg (orderFourMultiplierValue_nonneg t x hx)
        (orderFourSortedMultiplier_quadratic_nonneg t x)) (Finset.mem_univ s)
    rwa [hz] at h
  have hquad : quadraticValue ((orderFourMultiplierMatrix (orderFourSortedMultiplier s)).map
      (fun q : ℚ => (q : ℝ))) x ≤ 0 := nonpos_of_mul_nonpos_right hterm hweight
  have hv := (orderFourSortedMultiplier_lower s x).trans hquad
  have hvzero : (∑ i, x i^2)-(∑ i, x i)^2/16 = 0 := by
    have hn := orderFour_centered_nonneg x
    linarith
  rw [← sum_centered_sixteen] at hvzero
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => sq_nonneg (x i-(∑ j, x j)/16))).mp hvzero
  intro i
  have hxi := sub_eq_zero.mp (sq_eq_zero_iff.mp (hi i (Finset.mem_univ i)))
  simpa only [hsum] using hxi

end DittertRybin
