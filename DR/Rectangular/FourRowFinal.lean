import DR.Rectangular.FourRowFiniteFinal
import DR.Rectangular.FourRowTail
import DR.Square.OrderFourFinal

/-! Sharp K=4 maximization with exact uniform equality on every4×N board,
N≥4, and its transpose. The whole closed probability simplex is included. -/

namespace DittertRybin

theorem uniformMaximizer_orderFour_four_rows {n : ℕ} (hn : 4 ≤ n) :
    UniformMaximizer 4 n 4 := by
  by_cases hn4 : n = 4
  · subst n
    exact uniformMaximizer_four_four_four
  by_cases hn500 : n ≤ 500
  · exact uniformMaximizer_orderFour_four_rows_finite ⟨by omega,hn500⟩
  · exact uniformMaximizer_orderFour_four_rows_tail (by omega)

theorem fourRow_orderFour_closed_simplex {n : ℕ} (hn : 4 ≤ n)
    (P : Board 4 n) (hP : ∀ i j, 0 ≤ P i j) (hmass : totalMass P = 1) :
    separationProbability P 4 ≤
      1-(29/32 : ℝ)*(6/n-11/(n : ℝ)^2+6/(n : ℝ)^3) ∧
      (separationProbability P 4 =
        1-(29/32 : ℝ)*(6/n-11/(n : ℝ)^2+6/(n : ℝ)^3) ↔ P = uniformBoard 4 n) := by
  have hvalue := fourRow_failure_uniform (n := n) hn
  rw [separationProbability_uniform (by decide) (by omega)] at hvalue
  have hv : uniformSeparationValue 4 n 4 =
      1-(29/32 : ℝ)*(6/n-11/(n : ℝ)^2+6/(n : ℝ)^3) := by linarith
  simpa only [hv] using uniformMaximizer_orderFour_four_rows hn P ⟨hP,hmass⟩

theorem uniformMaximizer_orderFour_four_columns {m : ℕ} (hm : 4 ≤ m) :
    UniformMaximizer m 4 4 := by
  intro P hP
  have ht := uniformMaximizer_orderFour_four_rows hm P.transpose hP.transpose
  have hv : uniformSeparationValue 4 m 4 = uniformSeparationValue m 4 4 := by
    unfold uniformSeparationValue
    ring
  rw [separationProbability_transpose,hv] at ht
  refine ⟨ht.1,ht.2.trans ?_⟩
  constructor
  · intro he
    ext i j
    have hij := congrFun (congrFun he j) i
    simpa only [Matrix.transpose_apply,uniformBoard,mul_comm] using hij
  · intro he
    subst P
    ext i j
    simp only [Matrix.transpose_apply,uniformBoard,mul_comm]

theorem separationProbability_four_rows_lt_uniform_of_zero {n : ℕ} (hn : 4 ≤ n)
    {P : Board 4 n} (hP : IsProbability P) (i : Fin 4) (j : Fin n) (hzero : P i j = 0) :
    separationProbability P 4 < uniformSeparationValue 4 n 4 := by
  obtain ⟨hle,heq⟩ := uniformMaximizer_orderFour_four_rows hn P hP
  apply lt_of_le_of_ne hle
  intro he
  have hPU := heq.mp he
  have hpos : 0 < uniformBoard 4 n i j := by
    unfold uniformBoard
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  rw [hPU] at hzero
  exact (ne_of_gt hpos) hzero

/-- The release target includes both orientations of every four-row rectangle. -/
theorem uniform_maximum_four_rows {n : ℕ} (hn : 4 ≤ n) :
    UniformMaximizer 4 n 4 ∧ UniformMaximizer n 4 4 :=
  ⟨uniformMaximizer_orderFour_four_rows hn, uniformMaximizer_orderFour_four_columns hn⟩

end DittertRybin
