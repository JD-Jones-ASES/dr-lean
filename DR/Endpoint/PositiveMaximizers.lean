import DR.Endpoint.PositiveMaximizersGeometry

/-!
# Uniformity from positivity of all global maximizers

Maximize the squared norm on the full compact set of global maximizers. At a
positive member of this set, reverse column averaging is feasible and the
objective is exactly constant. Its strictly increasing squared norm excludes
unequal columns. Transposition excludes unequal rows. Finally, uniform's
minimum-norm property identifies every global maximizer, including any boundary
point in the original probability domain.
-/

namespace DittertRybin
open scoped BigOperators

/-- The entire probability-simplex level set, with no fixed support or positive floor. -/
def separationMaximizerLevel {m n : ℕ} (P : Board m n) (k : ℕ) : Set (Board m n) :=
  {Q | IsProbability Q ∧ separationProbability Q k = separationProbability P k}

theorem isCompact_separationMaximizerLevel {m n : ℕ} (P : Board m n) (k : ℕ) :
    IsCompact (separationMaximizerLevel P k) := by
  exact (isCompact_probabilitySimplex m n).inter_right
    (isClosed_eq (continuous_separationProbability k) continuous_const)

/-- A genuine global maximizer of greatest squared norm exists on the full maximizer set. -/
theorem exists_greatest_norm_globalMax {m n k : ℕ} {P : Board m n}
    (hP : IsProbability P) (hmax : IsSeparationGlobalMax P k) :
    ∃ Q : Board m n, IsProbability Q ∧ IsSeparationGlobalMax Q k ∧
      ∀ R : Board m n, IsProbability R → IsSeparationGlobalMax R k →
        orderThreeSquareSum R ≤ orderThreeSquareSum Q := by
  obtain ⟨Q, hQ, hnorm⟩ := (isCompact_separationMaximizerLevel P k).exists_isMaxOn
    ⟨P, hP, rfl⟩ continuous_orderThreeSquareSum.continuousOn
  have hQmax := hmax.of_value_eq hQ.2
  refine ⟨Q, hQ.1, hQmax, ?_⟩
  intro R hR hRmax
  apply hnorm
  exact ⟨hR, le_antisymm (hmax R hR) (hRmax P hP)⟩

/-- Positive maximum-norm global maximizers have identical columns. -/
theorem greatest_norm_globalMax_columns_eq {m n k : ℕ} {Q : Board m n}
    (hQ : IsProbability Q) (hmax : IsSeparationGlobalMax Q k) (hk : 2 ≤ k)
    (hpos : ∀ i j, 0 < Q i j)
    (hnorm : ∀ R : Board m n, IsProbability R → IsSeparationGlobalMax R k →
      orderThreeSquareSum R ≤ orderThreeSquareSum Q)
    (a b : Fin n) (i : Fin m) : Q i a = Q i b := by
  by_cases hab : a = b
  · subst b
    rfl
  obtain ⟨t, ht, hR⟩ := exists_negative_blend_probability hQ hpos a b hab
  have hRmax := hmax.same_support_blend hQ hk a b hab
    (fun h => iff_of_true (hpos h a) (hpos h b)) t
  have hle := hnorm _ hR hRmax
  rw [orderThreeSquareSum_blendColumns Q a b hab t] at hle
  have hcoeff : 0 < -(2 * t * (1 - t)) := by
    have h1 : 0 < 1 - t := by linarith
    have h2 : 2 * t < 0 := by linarith
    exact neg_pos.mpr (mul_neg_of_neg_of_pos h2 h1)
  have hsum0 : 0 ≤ ∑ h, (Q h a - Q h b) ^ 2 :=
    Finset.sum_nonneg fun h _ => sq_nonneg _
  have hsum : (∑ h, (Q h a - Q h b) ^ 2) = 0 := by
    have hprod : -(2 * t * (1 - t)) * (∑ h, (Q h a - Q h b) ^ 2) ≤ 0 := by
      linarith only [hle]
    have hsle : (∑ h, (Q h a - Q h b) ^ 2) ≤ 0 := by
      by_contra hnot
      exact (not_lt_of_ge hprod) (mul_pos hcoeff (lt_of_not_ge hnot))
    exact le_antisymm hsle hsum0
  have hi : (Q i a - Q i b) ^ 2 ≤ 0 := by
    calc
      _ ≤ ∑ h, (Q h a - Q h b) ^ 2 :=
        Finset.single_le_sum (fun h _ => sq_nonneg (Q h a - Q h b)) (Finset.mem_univ i)
      _ = 0 := hsum
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hi (sq_nonneg _)))

/-- The same maximum-norm choice works simultaneously in both orientations. -/
theorem greatest_norm_globalMax_eq_uniform {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    {Q : Board m n} (hQ : IsProbability Q) (hmax : IsSeparationGlobalMax Q k) (hk : 2 ≤ k)
    (hpos : ∀ i j, 0 < Q i j)
    (hnorm : ∀ R : Board m n, IsProbability R → IsSeparationGlobalMax R k →
      orderThreeSquareSum R ≤ orderThreeSquareSum Q) : Q = uniformBoard m n := by
  have hnormT : ∀ R : Board n m, IsProbability R → IsSeparationGlobalMax R k →
      orderThreeSquareSum R ≤ orderThreeSquareSum Q.transpose := by
    intro R hR hRmax
    simpa only [orderThreeSquareSum_transpose] using hnorm R.transpose hR.transpose hRmax.transpose
  apply eq_uniformBoard_of_equal_rows_columns hm hn hQ
  · intro i a b
    exact greatest_norm_globalMax_columns_eq hQ hmax hk hpos hnorm a b i
  · intro i h j
    exact greatest_norm_globalMax_columns_eq hQ.transpose hmax.transpose hk
      (fun a b => hpos b a) hnormT i h j

/-- Positivity of the complete global-maximizer set suffices for pointwise uniqueness. -/
theorem globalMax_eq_uniform_of_all_global_positive {m n k : ℕ}
    (hm : 0 < m) (hn : 0 < n) (hk : 2 ≤ k)
    (hpositive : ∀ P : Board m n, IsProbability P → IsSeparationGlobalMax P k →
      ∀ i j, 0 < P i j)
    {P : Board m n} (hP : IsProbability P) (hmax : IsSeparationGlobalMax P k) :
    P = uniformBoard m n := by
  obtain ⟨Q, hQ, hQmax, hnorm⟩ := exists_greatest_norm_globalMax hP hmax
  have hQU := greatest_norm_globalMax_eq_uniform hm hn hQ hQmax hk (hpositive Q hQ hQmax) hnorm
  apply (orderThreeSquareSum_le_uniform_iff hm hn hP).mp
  simpa only [hQU] using hnorm P hP hmax

/-- Boundary exclusion on actual global maximizers closes the full sharp Rybin inequality.
The hypothesis restricts maximizers only; the conclusion includes all zero-entry boards. -/
theorem uniform_maximizer_of_all_global_positive {m n k : ℕ}
    (hk : 2 ≤ k) (hkm : k ≤ m) (hkn : k ≤ n)
    (hpositive : ∀ P : Board m n, IsProbability P → IsSeparationGlobalMax P k →
      ∀ i j, 0 < P i j) : UniformMaximizer m n k := by
  have hm : 0 < m := by omega
  have hn : 0 < n := by omega
  apply uniform_maximizer_of_unique_global hm hn k
  intro P hP hmax
  exact globalMax_eq_uniform_of_all_global_positive hm hn hk hpositive hP hmax

end DittertRybin
