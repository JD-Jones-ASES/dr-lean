import DR.Rectangular.ThreeRowPositive

namespace DittertRybin.Tests
open scoped BigOperators

-- Repeated outcomes contribute the full derivative of a cubic monomial.
example (t : ℝ) : sampleMass (fun _ : Unit => (1 - t) * 2 + t * 5) (fun _ : Fin 3 => ()) =
    (2 + 3 * t) ^ 3 := by
  simp only [sampleMass, Fin.prod_univ_three]
  ring

-- Reject treating repeated samples as a quadratic monomial.
example : ¬ sampleMass (fun _ : Unit => (2 : ℝ)) (fun _ : Fin 3 => ()) = 4 := by
  norm_num [sampleMass, Fin.prod_univ_three]

-- The exact interpolation remains valid outside the probability segment.
example {m n : ℕ} (P Q : Board m n) :
    separationProbability (fun i j => 2 * P i j - Q i j) 3 =
      -4 * separationProbability P 3 + 5 * separationProbability Q 3 -
        4 * (∑ i, ∑ j, separationGradient P 3 i j * (Q i j - P i j)) -
        2 * (∑ i, ∑ j, separationGradient Q 3 i j * (Q i j - P i j)) := by
  have h := separationProbability_three_hermite P Q (-1)
  norm_num at h
  convert h using 1 <;> simp only [sub_eq_add_neg, neg_mul]

example {m n : ℕ} (P : Board m n) :
    orderThreeSquareSum (orderThreeCentered
      (fun i j => (1 - (1 / 2 : ℝ)) * uniformBoard m n i j + (1 / 2 : ℝ) * P i j)) =
      (1 / 4) * orderThreeSquareSum (orderThreeCentered P) := by
  rw [orderThreeCentered_squareSum_segment]
  norm_num

-- Full quantifiers: independent dimensions at least three, with no large-range criterion.
example {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) {P : Board m n}
    (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3) (hp : ∀ i j, 0 < P i j) :
    P = uniformBoard m n := hmax.eq_uniform_of_positive_three hP hm hn hp

example {n : ℕ} (hn : 3 ≤ n) {P : Board 3 n}
    (hP : IsProbability P) (hmax : IsSeparationGlobalMax P 3) (hp : ∀ i j, 0 < P i j) :
    ∀ i j, P i j = ((3 : ℝ) * n)⁻¹ := by
  rw [hmax.eq_uniform_of_positive_three hP (by norm_num) hn hp]
  intro i j
  rfl

#print axioms eventMass_three_hermite
#print axioms separationProbability_three_segment_flat
#print axioms IsSeparationGlobalMax.eq_uniform_of_positive_three
end DittertRybin.Tests
