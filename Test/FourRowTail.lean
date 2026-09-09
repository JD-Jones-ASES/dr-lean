import DR.Rectangular.FourRowTail

open DittertRybin DittertRybin.Certificates
open scoped BigOperators

/-- The visible target has only the dimension and original closed-simplex premises. -/
example {n : ℕ} (hn : 500 ≤ n) (P : Matrix (Fin 4) (Fin n) ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (hmass : (∑ i, ∑ j, P i j) = 1) :
    separationProbability P 4 ≤
      1 - (29/32 : ℝ) * (6/n - 11/(n:ℝ)^2 + 6/(n:ℝ)^3) ∧
    (separationProbability P 4 =
      1 - (29/32 : ℝ) * (6/n - 11/(n:ℝ)^2 + 6/(n:ℝ)^3) ↔
      ∀ i j, P i j = 1/(4*(n:ℝ))) := by
  have h := fourRow_orderFour_tail_closed_simplex hn P hP hmass
  refine ⟨h.1, h.2.trans ?_⟩
  constructor
  · intro he i j
    have hij := congrFun (congrFun he i) j
    simpa only [uniformBoard, one_div, Nat.cast_ofNat] using hij
  · intro he
    ext i j
    simpa only [uniformBoard, one_div, Nat.cast_ofNat] using he i j

example : UniformMaximizer 4 500 4 := uniformMaximizer_orderFour_four_rows_tail (by decide)
example : UniformMaximizer 500 4 4 := uniformMaximizer_orderFour_four_columns_tail (by decide)

/-- Every zero cell is strict; boundary probability distributions are included. -/
example {n : ℕ} (hn : 500 ≤ n) (P : Board 4 n) (hP : IsProbability P)
    (i : Fin 4) (j : Fin n) (hzero : P i j = 0) :
    separationProbability P 4 < uniformSeparationValue 4 n 4 := by
  obtain ⟨hle, heq⟩ := uniformMaximizer_orderFour_four_rows_tail hn P hP
  apply lt_of_le_of_ne hle
  intro he
  have hboard := heq.mp he
  have hij := congrFun (congrFun hboard i) j
  rw [hzero] at hij
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hu : 0 < uniformBoard 4 n i j := by unfold uniformBoard; positivity
  linarith

/-- Zero column mass causes no division premise in the actual gauge theorem. -/
example {n : ℕ} (P : Board 4 n) (hP : IsProbability P) (j : Fin n)
    (_hzero : colSum P j = 0) : fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j) :=
  fourRowGaugeColumn_minorant P hP j

/-- Distinct contender columns give a strictly positive actual sampling gain. -/
example {n : ℕ} (hn : 500 ≤ n) (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (a b : Fin n) (hab : a ≠ b) (hdiff : ∃ i, P i a ≠ P i b) :
    separationProbability P 4 < separationProbability (blendColumns P a b (1/2)) 4 := by
  obtain ⟨hm, hα, hν⟩ := fourRow_contender_deletion hn P hP hcont a b hab
  exact fourRow_separationProbability_blend_strict P hP.1 a b hab (1/2)
    (by norm_num) (by norm_num) hdiff hm hα hν

example : (∏ i : Fin 4, (![1,0,0,0] : Fin 4 → ℝ) i) ≠ 1/256 := by
  norm_num [Fin.prod_univ_succ]

#print axioms fourRowGauge_weighted_cauchy
#print axioms fourRowGaugeColumn_minorant
#print axioms fourRow_contender_deletion
#print axioms fourRow_equal_columns_separation
#print axioms fourRow_equal_columns_contender_uniform
#print axioms uniformMaximizer_orderFour_four_rows_tail
#print axioms uniformMaximizer_orderFour_four_columns_tail
#print axioms fourRow_orderFour_tail_closed_simplex
