import DR.Rectangular.FourRowTailProduct

/-!
# The four-row K=4 analytic tail

Every probability board with at least 500 columns supplies its own
concentration and deletion bounds. Strict actual column averaging forces
equal columns at every global maximum. The exact independent-coordinate
formula and row-product equality then force the uniform board.

The statement includes the full closed simplex and iff equality. It does
not include the separate finite certificate interval below 500 columns.
-/

namespace DittertRybin
open scoped BigOperators

/-- An actual contender supplies every premise of the strict pair-averaging bound. -/
theorem fourRow_contender_blend_gain {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (a b : Fin n) (hab : a ≠ b) :
    (13965659 / 1448000000 : ℝ) * (∑ i, (P i a - P i b) ^ 2) ≤
      separationProbability (blendColumns P a b (1/2)) 4 - separationProbability P 4 := by
  obtain ⟨hm, hα, hν⟩ := fourRow_contender_deletion hn P hP hcont a b hab
  have h := fourRow_separationProbability_blend_gain P hP.1 a b hab (1/2)
    (by norm_num) (by norm_num) hm hα hν
  norm_num at h ⊢
  exact h

theorem fourRowTail_globalMax_equal_columns {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hmax : ∀ Q : Board 4 n, IsProbability Q →
      separationProbability Q 4 ≤ separationProbability P 4) :
    ∀ i a b, P i a = P i b := by
  intro i a b
  by_cases hab : a = b
  · subst b
    rfl
  have hcont := hmax _ (uniformBoard_isProbability (by norm_num) (by omega))
  obtain ⟨hm, hα, hν⟩ := fourRow_contender_deletion hn P hP hcont a b hab
  exact fourRow_columns_eq_of_globalMax P hP hmax a b hm hα hν i

theorem fourRowTail_globalMax_uniform {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hmax : ∀ Q : Board 4 n, IsProbability Q →
      separationProbability Q 4 ≤ separationProbability P 4) :
    P = uniformBoard 4 n :=
  fourRow_equal_columns_contender_uniform (by omega) P hP
    (fourRowTail_globalMax_equal_columns hn P hP hmax)
    (hmax _ (uniformBoard_isProbability (by norm_num) (by omega)))

/-- Full closed-simplex sharp K=4 inequality and exact uniform equality for N ≥ 500. -/
theorem uniformMaximizer_orderFour_four_rows_tail {n : ℕ} (hn : 500 ≤ n) :
    UniformMaximizer 4 n 4 :=
  uniform_maximizer_of_unique_global (by norm_num) (by omega) 4
    (fun P hP hmax => fourRowTail_globalMax_uniform hn P hP hmax)

/-- The sharp value written explicitly in the column count, on the full closed simplex. -/
theorem fourRow_orderFour_tail_closed_simplex {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P 4 ≤
      1 - (29/32 : ℝ) * (6/n - 11/(n:ℝ)^2 + 6/(n:ℝ)^3) ∧
    (separationProbability P 4 =
      1 - (29/32 : ℝ) * (6/n - 11/(n:ℝ)^2 + 6/(n:ℝ)^3) ↔
      P = uniformBoard 4 n) := by
  have hvalue := fourRow_failure_uniform (n := n) (by omega)
  rw [separationProbability_uniform (by norm_num) (by omega)] at hvalue
  have hv : uniformSeparationValue 4 n 4 =
      1 - (29/32 : ℝ) * (6/n - 11/(n:ℝ)^2 + 6/(n:ℝ)^3) := by linarith
  simpa only [hv] using uniformMaximizer_orderFour_four_rows_tail hn P ⟨hP, hmass⟩

/-- The transposed analytic tail has the same complete equality statement. -/
theorem uniformMaximizer_orderFour_four_columns_tail {m : ℕ} (hm : 500 ≤ m) :
    UniformMaximizer m 4 4 := by
  apply uniform_maximizer_of_unique_global (by omega) (by norm_num) 4
  intro P hP hmax
  have hmaxT : ∀ Q : Board 4 m, IsProbability Q →
      separationProbability Q 4 ≤ separationProbability P.transpose 4 := by
    intro Q hQ
    simpa only [separationProbability_transpose] using hmax Q.transpose hQ.transpose
  have he := fourRowTail_globalMax_uniform hm P.transpose hP.transpose hmaxT
  ext i j
  have hij := congrFun (congrFun he j) i
  simpa only [Matrix.transpose_apply, uniformBoard, mul_comm] using hij

end DittertRybin
