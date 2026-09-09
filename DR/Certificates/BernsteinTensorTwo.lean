import DR.Certificates.Bernstein
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-! Exact two-variable tensor expansion for the order-five rational certificates. -/

namespace DittertRybin.Certificates

open scoped BigOperators
open MvPolynomial
noncomputable section

theorem tensorPolynomial_two (n m : ℕ) (c : Fin (n + 1) → Fin (m + 1) → ℚ) :
    tensorPolynomial ![n, m] (fun a => c (a 0) (a 1)) =
      ∑ i : Fin (n + 1), ∑ j : Fin (m + 1), C (c i j) *
        ((C (n.choose i : ℚ) * X (0 : Fin 2) ^ (i : ℕ) * (1 - X 0) ^ (n - i)) *
         (C (m.choose j : ℚ) * X (1 : Fin 2) ^ (j : ℕ) * (1 - X 1) ^ (m - j))) := by
  unfold tensorPolynomial
  trans ∑ p : Fin (n + 1) × Fin (m + 1), C (c p.1 p.2) *
    ((C (n.choose p.1 : ℚ) * X (0 : Fin 2) ^ (p.1 : ℕ) * (1 - X 0) ^ (n - p.1)) *
     (C (m.choose p.2 : ℚ) * X (1 : Fin 2) ^ (p.2 : ℕ) * (1 - X 1) ^ (m - p.2)))
  · apply Fintype.sum_equiv (piFinTwoEquiv (fun i => Fin ((![n, m] : Fin 2 → ℕ) i + 1)))
    intro a
    simp [tensorBasis, Fin.prod_univ_two, piFinTwoEquiv]
    rfl
  · exact Fintype.sum_prod_type _

end
end DittertRybin.Certificates
