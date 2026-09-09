import DR.Square.AllOrders

/-! Expanded release-target scope and exact equality, including order one. -/

namespace DittertRybin.Tests
open scoped BigOperators

example {n : ℕ} (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : (∑ i, ∑ j, A i j) = (n : ℝ)) :
    (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent ≤
      2 - (n.factorial : ℝ) / (n : ℝ) ^ n ∧
    ((∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent =
      2 - (n.factorial : ℝ) / (n : ℝ) ^ n ↔ A = fun _ _ => (n : ℝ)⁻¹) :=
  dittert_unique_maximum hn A hA hmass

example {n : ℕ} (hn : 0 < n) (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hmass : (∑ i, ∑ j, P i j) = 1) :
    separationProbability P n ≤ dittertConstant n * (2-dittertConstant n) ∧
      (separationProbability P n = dittertConstant n * (2-dittertConstant n) ↔
        P = fun _ _ => ((n:ℝ)*n)⁻¹) := by
  have h := uniform_maximum_square_endpoint hn P ⟨hP,hmass⟩
  rwa [uniformSeparationValue_endpoint] at h

example : DittertMaximizer 1 := dittert_unique_maximum (by decide)
example : DittertMaximizer 5 := dittert_unique_maximum (by decide)
example : DittertMaximizer 6 := dittert_unique_maximum (by decide)
example : DittertMaximizer 100 := dittert_unique_maximum (by decide)

#print axioms dittert_unique_maximum
#print axioms uniform_maximum_square_endpoint

end DittertRybin.Tests
