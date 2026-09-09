import DR.Rectangular.ThreeRowNormalForm

/-! Exact least-norm support normal forms, with both original zeros and positive floors retained. -/

namespace DittertRybin
open scoped BigOperators

/-- A finite board has a common positive lower bound on all of its positive entries. -/
theorem exists_sameSupportFloor {m n : ℕ} (P : Board m n) :
    ∃ ε : ℝ, 0 < ε ∧ SameSupportFloor P ε P := by
  classical
  let S : Finset ℝ := insert 1 ((Finset.univ.filter
    (fun a : Fin m × Fin n => 0 < P a.1 a.2)).image (fun a => P a.1 a.2))
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  have hpos : 0 < S.min' hS := by
    have hmem := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hmem with heq | himage
    · rw [heq]
      norm_num
    · obtain ⟨a, ha, heq⟩ := Finset.mem_image.mp himage
      rw [← heq]
      exact (Finset.mem_filter.mp ha).2
  refine ⟨S.min' hS, hpos, ?_⟩
  intro i j
  refine ⟨fun h => h, fun hp => ?_⟩
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩)

theorem SameSupportFloor.transpose {m n : ℕ} {P Q : Board m n} {ε : ℝ}
    (h : SameSupportFloor P ε Q) : SameSupportFloor P.transpose ε Q.transpose := by
  intro i j
  exact h j i

theorem orderThreeSquareSum_transpose {m n : ℕ} (P : Board m n) :
    orderThreeSquareSum P.transpose = orderThreeSquareSum P := by
  unfold orderThreeSquareSum
  exact Finset.sum_comm

/-- At a least-norm maximizer inside a fixed support class, equal-support columns coincide. -/
theorem least_norm_supported_columns_eq {m n k : ℕ} {P Q : Board m n} {ε : ℝ}
    (hP : IsProbability P) (hmax : IsSeparationGlobalMax P k) (hk : 2 ≤ k) (hε : 0 < ε)
    (hQ : Q ∈ supportedMaximizerSet P k ε)
    (hmin : ∀ R ∈ supportedMaximizerSet P k ε, orderThreeSquareSum Q ≤ orderThreeSquareSum R)
    (a b : Fin n) (hsupport : ∀ i, 0 < P i a ↔ 0 < P i b) : ∀ i, Q i a = Q i b := by
  by_cases hab : a = b
  · subst b
    intro i
    rfl
  have hQmax : IsSeparationGlobalMax Q k := hmax.of_value_eq hQ.2.1
  have hQsupport (i : Fin m) : 0 < Q i a ↔ 0 < Q i b :=
    ((hQ.2.2).support_iff hP.1 hε i a).trans
      ((hsupport i).trans ((hQ.2.2).support_iff hP.1 hε i b).symm)
  have hR : blendColumns Q a b (1 / 2) ∈ supportedMaximizerSet P k ε := by
    refine ⟨blendColumns_isProbability hQ.1 a b hab (1 / 2) (by norm_num) (by norm_num), ?_, ?_⟩
    · exact (hQmax.same_support_blend_flat hQ.1 hk a b hab hQsupport (1 / 2)).trans hQ.2.1
    · exact hQ.2.2.blendColumns hP.1 a b hab hsupport (by norm_num) (by norm_num)
  have hnorm := hmin _ hR
  rw [orderThreeSquareSum_blend_midpoint Q a b hab] at hnorm
  have hdist : (∑ i, (Q i a - Q i b) ^ 2) = 0 := by
    apply le_antisymm (by linarith only [hnorm])
    exact Finset.sum_nonneg fun i _ => sq_nonneg (Q i a - Q i b)
  intro i
  have hi : (Q i a - Q i b) ^ 2 ≤ 0 := by
    calc
      _ ≤ ∑ h, (Q h a - Q h b) ^ 2 :=
        Finset.single_le_sum (fun h _ => sq_nonneg (Q h a - Q h b)) (Finset.mem_univ i)
      _ = 0 := hdist
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _)))

/-- Both row and column normal forms hold at the same support-preserving maximizer. -/
theorem exists_same_support_normal_form {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (hmax : IsSeparationGlobalMax P k) (hk : 2 ≤ k) :
    ∃ (ε : ℝ) (Q : Board m n), 0 < ε ∧ IsProbability Q ∧ IsSeparationGlobalMax Q k ∧
      SameSupportFloor P ε Q ∧
      (∀ a b, (∀ i, 0 < P i a ↔ 0 < P i b) → ∀ i, Q i a = Q i b) ∧
      (∀ a b, (∀ j, 0 < P a j ↔ 0 < P b j) → ∀ j, Q a j = Q b j) := by
  obtain ⟨ε, hε, hfloor⟩ := exists_sameSupportFloor P
  obtain ⟨Q, hQ, hmin⟩ := exists_least_norm_supportedMaximizer hP hfloor
  refine ⟨ε, Q, hε, hQ.1, hmax.of_value_eq hQ.2.1, hQ.2.2, ?_, ?_⟩
  · exact least_norm_supported_columns_eq hP hmax hk hε hQ hmin
  · have hQT : Q.transpose ∈ supportedMaximizerSet P.transpose k ε := by
      refine ⟨hQ.1.transpose, ?_, hQ.2.2.transpose⟩
      simpa only [separationProbability_transpose] using hQ.2.1
    have hminT : ∀ R ∈ supportedMaximizerSet P.transpose k ε,
        orderThreeSquareSum Q.transpose ≤ orderThreeSquareSum R := by
      intro R hR
      have hRT : R.transpose ∈ supportedMaximizerSet P k ε := by
        refine ⟨hR.1.transpose, ?_, ?_⟩
        · simpa only [separationProbability_transpose] using hR.2.1
        · exact hR.2.2.transpose
      simpa only [orderThreeSquareSum_transpose] using hmin R.transpose hRT
    exact least_norm_supported_columns_eq hP.transpose hmax.transpose hk hε hQT hminT

/-- A positive global maximizer guarantees that uniform is also globally maximal.
This statement alone does not yet identify the original positive maximizer. -/
theorem IsSeparationGlobalMax.uniform_of_positive {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P) (hk : 2 ≤ k)
    (hm : 0 < m) (hn : 0 < n) (hpos : ∀ i j, 0 < P i j) :
    IsSeparationGlobalMax (uniformBoard m n) k := by
  obtain ⟨ε, Q, hε, hQ, hQmax, hfloor, hcol, hrow⟩ := exists_same_support_normal_form hP hmax hk
  have hc (i : Fin m) (a b : Fin n) : Q i a = Q i b :=
    hcol a b (fun h => iff_of_true (hpos h a) (hpos h b)) i
  have hr (i h : Fin m) (j : Fin n) : Q i j = Q h j :=
    hrow i h (fun a => iff_of_true (hpos i a) (hpos h a)) j
  have hQU := eq_uniformBoard_of_equal_rows_columns hm hn hQ hc hr
  simpa only [hQU] using hQmax

theorem IsSeparationGlobalMax.value_eq_uniform_of_positive {m n k : ℕ} {P : Board m n}
    (hmax : IsSeparationGlobalMax P k) (hP : IsProbability P) (hk : 2 ≤ k)
    (hm : 0 < m) (hn : 0 < n) (hpos : ∀ i j, 0 < P i j) :
    separationProbability P k = uniformSeparationValue m n k := by
  have hU := hmax.uniform_of_positive hP hk hm hn hpos
  have heq : separationProbability P k = separationProbability (uniformBoard m n) k :=
    le_antisymm (hU P hP) (hmax _ (uniformBoard_isProbability hm hn))
  exact heq.trans (separationProbability_uniform hm hn)

end DittertRybin
