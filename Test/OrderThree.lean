import DR.Square.OrderThreeFinal

/-! Expanded domain and exact endpoint controls for order three. -/

open scoped BigOperators
open DittertRybin

example (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hm : (∑ i, ∑ j, A i j) = 3) :
    (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent ≤ 16 / 9 ∧
      ((∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent = 16 / 9 ↔
        A = fun _ _ => 1 / 3) := by
  have h := dittert_order_three A hA hm
  norm_num [dittertFunctional, dittertConstant, uniformDittertMatrix, rowSum, colSum] at h ⊢
  have hu : uniformDittertMatrix 3 = (fun _ _ => (1 / 3 : ℝ)) := by
    ext i j
    norm_num [uniformDittertMatrix]
  rwa [hu] at h

example : UniformMaximizer 3 3 3 := uniformMaximizer_three_three_three

example : uniformSeparationValue 3 3 3 = 32 / 81 := by
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

#print axioms DittertRybin.dittert_order_three
#print axioms DittertRybin.uniformMaximizer_three_three_three
