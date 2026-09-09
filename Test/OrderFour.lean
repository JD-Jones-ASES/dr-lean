import DR.Square.OrderFourFinal

/-! Expanded domain, boundary strictness, and sharp-constant controls. -/

open scoped BigOperators
open DittertRybin

example (A : Matrix (Fin 4) (Fin 4) ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (hm : (∑ i, ∑ j, A i j) = 4) :
    (∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent ≤ 61 / 32 ∧
      ((∏ i, ∑ j, A i j) + (∏ j, ∑ i, A i j) - A.permanent = 61 / 32 ↔
        A = fun _ _ => 1 / 4) := by
  have h := dittert_order_four A hA hm
  norm_num [dittertFunctional, dittertConstant, rowSum, colSum] at h ⊢
  have hu : uniformDittertMatrix 4 = (fun _ _ => (1 / 4 : ℝ)) := by
    ext i j
    norm_num [uniformDittertMatrix]
  rwa [hu] at h

example : UniformMaximizer 4 4 4 := uniformMaximizer_four_four_four

example : separationProbability (uniformBoard 4 4) 4 = 183 / 1024 :=
  orderFour_uniform_value

example : ¬ (∀ P : Board 4 4, IsProbability P →
    separationProbability P 4 ≤ (182 / 1024 : ℝ)) := by
  intro h
  have h' := h (uniformBoard 4 4) (uniformBoard_isProbability (by decide) (by decide))
  rw [orderFour_uniform_value] at h'
  norm_num at h'

example (P : Board 4 4) (hP : IsProbability P) (i j : Fin 4) (hzero : P i j = 0) :
    separationProbability P 4 < 183 / 1024 := by
  apply lt_of_le_of_ne (orderFour_probability_bound P hP)
  intro heq
  have hu := (orderFour_probability_equality P hP).mp heq
  have h := congrFun (congrFun hu i) j
  norm_num [uniformBoard, hzero] at h

#print axioms DittertRybin.orderFourSextic_multiset_orbit
#print axioms DittertRybin.orderFourSextic_certificate_identity
#print axioms DittertRybin.orderFour_probability_equality
#print axioms DittertRybin.dittert_order_four
#print axioms DittertRybin.uniformMaximizer_four_four_four
