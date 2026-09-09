import DR.Rectangular.FourRowGaugeMinorant
import DR.Endpoint.Normalization
import DR.Maximizers

/-! The exact sampling functional when all columns coincide. The remaining
row equality is the existing boundary-safe elementary-symmetric equality
theorem; no full-support premise is introduced. -/

namespace DittertRybin
open scoped BigOperators

theorem fourRow_equal_columns_entries {n : ℕ} (hn : 0 < n) (P : Board 4 n)
    (hc : ∀ i a b, P i a = P i b) (i : Fin 4) (j : Fin n) :
    P i j = rowSum P i / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he (a : Fin n) : P i a = P i j := hc i a j
  have hsum : rowSum P i = (n : ℝ) * P i j := by
    simp only [rowSum, he, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  field_simp

/-- Inclusive OR factors into the two independent coordinate events for equal columns. -/
theorem fourRow_equal_columns_separation {n : ℕ} (hn : 0 < n) (P : Board 4 n)
    (hP : IsProbability P) (hc : ∀ i a b, P i a = P i b) :
    separationProbability P 4 =
      24 * (∏ i, rowSum P i) + distinctUniformProbability n 4 -
        24 * (∏ i, rowSum P i) * distinctUniformProbability n 4 := by
  classical
  have hp := fourRow_equal_columns_entries hn P hc
  have hcol (j : Fin n) : colSum P j = 1 / (n : ℝ) := by
    simp only [colSum, hp, ← Finset.sum_div]
    rw [show (∑ i, rowSum P i) = 1 from hP.2]
  rw [separationProbability_eq_embedding_sums]
  have hrows : (∑ r : Fin 4 ↪ Fin 4, ∏ t, rowSum P (r t)) =
      24 * ∏ i, rowSum P i := by
    simp [prod_comp_self_embedding, Fintype.card_embedding_eq, nsmul_eq_mul]
  have hcols : (∑ c : Fin 4 ↪ Fin n, ∏ t, colSum P (c t)) =
      distinctUniformProbability n 4 := by
    simp [hcol, Fintype.card_embedding_eq, nsmul_eq_mul, distinctUniformProbability,
      div_eq_mul_inv]
  have hboth : (∑ q : (Fin 4 ↪ Fin 4) × (Fin 4 ↪ Fin n), ∏ t, P (q.1 t) (q.2 t)) =
      24 * (∏ i, rowSum P i) * distinctUniformProbability n 4 := by
    simp only [hp, Finset.prod_div_distrib, prod_comp_self_embedding,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_embedding_eq, Nat.descFactorial_self, Nat.cast_mul, nsmul_eq_mul]
    norm_num [Nat.factorial, distinctUniformProbability]
    ring
  rw [hrows, hcols, hboth]

theorem fourRow_product_eq_uniform_iff (r : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i)
    (hs : ∑ i, r i = 1) : (∏ i, r i) = 1/256 ↔ ∀ i, r i = 1/4 := by
  have h := normalizedElementarySuccess_eq_one_iff (d := 4) (k := 4)
    hr hs (by norm_num) (by norm_num)
  simp only [normalizedElementarySuccess, elementaryMean, elementarySymmetric_top] at h
  norm_num at h
  constructor
  · intro hp
    apply h.mp
    rw [hp]
    norm_num
  · intro he
    norm_num [he]

/-- A contender with equal columns has uniform rows and hence uniform cells. -/
theorem fourRow_equal_columns_contender_uniform {n : ℕ} (hn : 0 < n)
    (P : Board 4 n) (hP : IsProbability P)
    (hc : ∀ i a b, P i a = P i b)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4) :
    P = uniformBoard 4 n := by
  have hF := fourRow_equal_columns_separation hn P hP hc
  have hU := separationProbability_uniform (k := 4) (by norm_num : 0 < 4) hn
  rw [uniformSeparationValue_rectangular_endpoint] at hU
  norm_num [dittertConstant, Nat.factorial] at hU
  have hb := distinctUniformProbability_lt_one (k := 4) hn (by norm_num)
  have hp := fourRow_product_le_uniform (rowSum P) (rowSum_nonneg hP.1) hP.2
  have hprod : (∏ i, rowSum P i) = 1/256 := by
    rw [hF, hU] at hcont
    nlinarith
  have hr := (fourRow_product_eq_uniform_iff (rowSum P) (rowSum_nonneg hP.1) hP.2).mp hprod
  ext i j
  rw [fourRow_equal_columns_entries hn P hc, hr]
  simp only [uniformBoard]
  norm_num
  ring

end DittertRybin
