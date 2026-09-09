import DR.Certificates.Bernstein

/-! Strict positivity of a complete Bernstein blend, including every cube face. -/

namespace DittertRybin.Certificates
open scoped BigOperators

theorem exists_bernsteinWeight_pos (n : ℕ) (x : ℝ) :
    ∃ i : Fin (n + 1), 0 < bernsteinWeight n i x := by
  by_contra h
  push Not at h
  have hs := Finset.sum_nonpos fun i (_ : i ∈ Finset.univ) => h i
  rw [bernsteinWeight_sum] at hs
  norm_num at hs

/-- Every coefficient is positive and the complete tensor weights sum to one. -/
theorem bernstein_two_positive_blend {n m : ℕ}
    (c : Fin (n + 1) → Fin (m + 1) → ℝ) (hc : ∀ i j, 0 < c i j)
    (x y : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    0 < ∑ i, ∑ j, c i j * bernsteinWeight n i x * bernsteinWeight m j y := by
  have hnon (i : Fin (n + 1)) (j : Fin (m + 1)) :
      0 ≤ c i j * bernsteinWeight n i x * bernsteinWeight m j y :=
    mul_nonneg (mul_nonneg (hc i j).le (bernsteinWeight_nonneg _ _ hx hx1))
      (bernsteinWeight_nonneg _ _ hy hy1)
  obtain ⟨i, hi⟩ := exists_bernsteinWeight_pos n x
  obtain ⟨j, hj⟩ := exists_bernsteinWeight_pos m y
  have hp := mul_pos (mul_pos (hc i j) hi) hj
  have hinner := Finset.single_le_sum (fun j _ => hnon i j) (Finset.mem_univ j)
  have houter :
      (∑ j, c i j * bernsteinWeight n i x * bernsteinWeight m j y) ≤
      ∑ i, ∑ j, c i j * bernsteinWeight n i x * bernsteinWeight m j y :=
    Finset.single_le_sum
      (fun i _ => Finset.sum_nonneg fun j _ => hnon i j) (Finset.mem_univ i)
  exact hp.trans_le (hinner.trans houter)

end DittertRybin.Certificates
