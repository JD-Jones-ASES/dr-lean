import DR.Rectangular.ThreeRowTwoDoubletNormal
import DR.Rectangular.ThreeRowThreeDoublets
import DR.Rectangular.ThreeRowPositive

/-! The complete three-row, three-sample theorem on the closed probability simplex. -/
namespace DittertRybin

/-- Every actual three-row global maximizer is strictly positive: all zero-support
families are eliminated, without a column-count bound or support restriction. -/
theorem IsSeparationGlobalMax.threeRow_positive {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n) :
    ∀ r j, 0 < P r j := by
  intro r j
  by_contra hnot
  have hzero : P r j = 0 := le_antisymm (le_of_not_gt hnot) (hP.1 r j)
  rcases hmax.threeRow_columns_full_or_doublet hP hn j with hf | ⟨i,hi⟩
  · exact (ne_of_gt (hf r)) hzero
  have hother : ∃ h b, ThreeRowDoublet P h b ∧ h ≠ i := by
    by_contra hnother
    apply hmax.threeRow_not_single_doublet_type hP hn i j hi
    intro h b hb
    by_contra hne
    exact hnother ⟨h,b,hb,hne⟩
  obtain ⟨h,b,hb,hhi⟩ := hother
  have htypes (t : Fin 3) (c : Fin n) (hc : ThreeRowDoublet P t c) : t = i ∨ t = h := by
    by_cases hti : t = i
    · exact Or.inl hti
    by_cases hth : t = h
    · exact Or.inr hth
    have hex : ∀ u : Fin 3, u = i ∨ u = h ∨ u = t :=
      (by decide : ∀ i h t : Fin 3, h ≠ i → t ≠ i → t ≠ h → ∀ u, u = i ∨ u = h ∨ u = t)
        i h t hhi hti hth
    apply False.elim
    apply hmax.threeRow_not_all_doublet_types hP hn
    intro u
    rcases hex u with hu | hu | hu
    · exact ⟨j, hu ▸ hi⟩
    · exact ⟨b, hu ▸ hb⟩
    · exact ⟨c, hu ▸ hc⟩
  exact hmax.threeRow_not_two_doublet_types hP hn i h hhi.symm j b hi hb htypes

/-- Uniform is the only actual global maximizer in three rows, for every n≥3. -/
theorem IsSeparationGlobalMax.threeRow_eq_uniform {n : ℕ} {P : Board 3 n}
    (hmax : IsSeparationGlobalMax P 3) (hP : IsProbability P) (hn : 3 ≤ n) :
    P = uniformBoard 3 n :=
  hmax.eq_uniform_of_positive_three hP (by norm_num) hn (hmax.threeRow_positive hP hn)

/-- The full three-row K=3 uniform maximum, including the equality case and all zero entries. -/
theorem uniformMaximizer_three_rows {n : ℕ} (hn : 3 ≤ n) : UniformMaximizer 3 n 3 := by
  obtain ⟨Q,hQ,hQmax⟩ := exists_separation_maximizer (by norm_num : 0 < 3) (by omega : 0 < n) 3
  have hQmax' : IsSeparationGlobalMax Q 3 := hQmax
  have hQU := hQmax'.threeRow_eq_uniform hQ hn
  have hU : IsSeparationGlobalMax (uniformBoard 3 n) 3 := hQU ▸ hQmax'
  intro P hP
  have hval := separationProbability_uniform (m := 3) (n := n) (k := 3) (by norm_num) (by omega)
  refine ⟨(hU P hP).trans_eq hval, ?_⟩
  constructor
  · intro heq
    have hPmax : IsSeparationGlobalMax P 3 := by
      intro R hR
      rw [heq, ← hval]
      exact hU R hR
    exact hPmax.threeRow_eq_uniform hP hn
  · intro heq
    simpa only [heq] using hval

/-- The transposed theorem has the same full domain and equality case. -/
theorem uniformMaximizer_three_columns {m : ℕ} (hm : 3 ≤ m) : UniformMaximizer m 3 3 := by
  apply uniform_maximizer_of_unique_global (by omega) (by norm_num) 3
  intro P hP hmax
  have hmax' : IsSeparationGlobalMax P 3 := hmax
  have heq := hmax'.transpose.threeRow_eq_uniform hP.transpose hm
  funext i j
  have hij := congrFun (congrFun heq j) i
  simpa only [Matrix.transpose_apply, uniformBoard, mul_comm] using hij

/-- Any zero entry causes a strict loss in every three-row rectangle with n≥3. -/
theorem separationProbability_three_rows_lt_uniform_of_zero {n : ℕ} (hn : 3 ≤ n)
    {P : Board 3 n} (hP : IsProbability P) (i : Fin 3) (j : Fin n) (hzero : P i j = 0) :
    separationProbability P 3 < uniformSeparationValue 3 n 3 := by
  obtain ⟨hle,heq⟩ := uniformMaximizer_three_rows hn P hP
  apply lt_of_le_of_ne hle
  intro he
  have hPU := heq.mp he
  have hpos : 0 < uniformBoard 3 n i j := by
    unfold uniformBoard
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  rw [hPU] at hzero
  exact (ne_of_gt hpos) hzero

end DittertRybin
