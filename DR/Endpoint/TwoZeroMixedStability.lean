import DR.Endpoint.TwoZeroMixedDefinitions
import DR.Endpoint.StableQuadratic

/-! Actual derivative closure through the full mixed-quadratic reduction.
Nonnegative matrices with zero rows or columns remain covered. -/

namespace DittertRybin

theorem permanentQuadraticReduce_homogeneous (n : ℕ)
    {p : MvPolynomial (Fin (n+2)) ℝ} (hp : p.IsHomogeneous (n+2)) :
    (permanentQuadraticReduce n p).IsHomogeneous 2 := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ih (capacityReduce_isHomogeneous hp)

theorem permanentQuadraticReduce_nonnegative (n : ℕ)
    {p : MvPolynomial (Fin (n+2)) ℝ} (hp : HasNonnegativeCoefficients p) :
    HasNonnegativeCoefficients (permanentQuadraticReduce n p) := by
  induction n with
  | zero => exact hp
  | succ n ih => exact ih (capacityReduce_nonnegative hp)

theorem permanentQuadraticReduce_zero_or_hStable (n : ℕ)
    {p : MvPolynomial (Fin (n+2)) ℝ} (hhom : p.IsHomogeneous (n+2))
    (hc : HasNonnegativeCoefficients p) (hp : p = 0 ∨ HStable p) :
    permanentQuadraticReduce n p = 0 ∨ HStable (permanentQuadraticReduce n p) := by
  induction n with
  | zero => exact hp
  | succ n ih =>
    exact ih (capacityReduce_isHomogeneous hhom) (capacityReduce_nonnegative hc)
      (capacityReduce_zero_or_hStable hhom hc hp)

/-- A nonnegative row-product polynomial either vanishes identically or is
stable. This includes an arbitrary zero row without regularization. -/
theorem matrixProductPolynomial_zero_or_hStable {n : ℕ} {A : Board n n}
    (hA : ∀ i j, 0 ≤ A i j) :
    matrixProductPolynomial A = 0 ∨ HStable (matrixProductPolynomial A) := by
  classical
  by_cases hr : ∀ i, 0 < rowSum A i
  · exact Or.inr (matrixProductPolynomial_hStable hA hr)
  · obtain ⟨i, hi⟩ := not_forall.mp hr
    have hz : rowSum A i = 0 := le_antisymm (le_of_not_gt hi)
      (Finset.sum_nonneg fun j _ => hA i j)
    have heach (j) : A i j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => hA i j)).mp hz
        j (Finset.mem_univ j)
    left
    unfold matrixProductPolynomial
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [heach])

theorem permanentMixedQuadratic_homogeneous {n : ℕ} (A : Board (n+2) (n+2)) :
    (permanentMixedQuadratic A).IsHomogeneous 2 :=
  permanentQuadraticReduce_homogeneous n (matrixProductPolynomial_isHomogeneous A.transpose)

theorem permanentMixedQuadratic_zero_or_hStable {n : ℕ} {A : Board (n+2) (n+2)}
    (hA : ∀ i j, 0 ≤ A i j) :
    permanentMixedQuadratic A = 0 ∨ HStable (permanentMixedQuadratic A) :=
  permanentQuadraticReduce_zero_or_hStable n
    (matrixProductPolynomial_isHomogeneous A.transpose)
    (matrixProductPolynomial_nonnegative (fun i j => hA j i))
    (matrixProductPolynomial_zero_or_hStable (fun i j => hA j i))

theorem permanentMixedQuadratic_discriminant {n : ℕ} {A : Board (n+2) (n+2)}
    (hA : ∀ i j, 0 ≤ A i j) :
    4*(permanentMixedQuadratic A).coeff (Finsupp.single 0 2)*
      (permanentMixedQuadratic A).coeff (Finsupp.single 1 2) ≤ A.permanent^2 := by
  have h := stable_fin_two_quadratic_discriminant (permanentMixedQuadratic_homogeneous A)
    (permanentMixedQuadratic_zero_or_hStable hA)
  rwa [permanentMixedQuadratic_coeff11] at h

end DittertRybin
