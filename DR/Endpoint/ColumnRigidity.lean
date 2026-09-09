import DR.Endpoint.Contenders
import DR.EndpointIdentity
import DR.Maximizers

/-!
# Closing one-sided endpoint averaging

For m draws, equal columns leave only the product of the m row masses.
Its sharp equality theorem forces uniform rows. Thus column rigidity of
global maximizers alone closes endpoint averaging, including zero entries
in the original probability simplex.
-/

namespace DittertRybin
open scoped BigOperators

theorem endpoint_equal_columns_entries {m n : ℕ} (hn : 0 < n) (P : Board m n)
    (hc : ∀ i a b, P i a = P i b) (i : Fin m) (j : Fin n) :
    P i j = rowSum P i / n := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have he (a : Fin n) : P i a = P i j := hc i a j
  have hsum : rowSum P i = (n : ℝ) * P i j := by
    simp only [rowSum, he, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum]
  field_simp

/-- Equal columns give the exact inclusive-OR product formula. -/
theorem endpoint_equal_columns_separation {m n : ℕ} (hn : 0 < n) (P : Board m n)
    (hP : IsProbability P) (hc : ∀ i a b, P i a = P i b) :
    separationProbability P m =
      (m.factorial : ℝ) * (∏ i, rowSum P i) + distinctUniformProbability n m -
        (m.factorial : ℝ) * (∏ i, rowSum P i) * distinctUniformProbability n m := by
  classical
  have hp := endpoint_equal_columns_entries hn P hc
  have hcol (j : Fin n) : colSum P j = 1 / (n : ℝ) := by
    simp only [colSum, hp, ← Finset.sum_div]
    rw [show (∑ i, rowSum P i) = 1 from hP.2]
  rw [separationProbability_eq_embedding_sums]
  have hrows : (∑ r : Fin m ↪ Fin m, ∏ t, rowSum P (r t)) =
      (m.factorial : ℝ) * ∏ i, rowSum P i := by
    simp [prod_comp_self_embedding, Fintype.card_embedding_eq, nsmul_eq_mul,
      Nat.descFactorial_self]
  have hcols : (∑ c : Fin m ↪ Fin n, ∏ t, colSum P (c t)) =
      distinctUniformProbability n m := by
    simp [hcol, Fintype.card_embedding_eq, nsmul_eq_mul, distinctUniformProbability,
      div_eq_mul_inv]
  have hboth : (∑ q : (Fin m ↪ Fin m) × (Fin m ↪ Fin n), ∏ t, P (q.1 t) (q.2 t)) =
      (m.factorial : ℝ) * (∏ i, rowSum P i) * distinctUniformProbability n m := by
    simp only [hp, Finset.prod_div_distrib, prod_comp_self_embedding,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_embedding_eq, Fintype.card_fin, Nat.descFactorial_self,
      Nat.cast_mul, nsmul_eq_mul]
    unfold distinctUniformProbability
    ring
  rw [hrows, hcols, hboth]

theorem endpoint_factorial_rowProduct {m n : ℕ} (hm : 0 < m) (P : Board m n) :
    (m.factorial : ℝ) * (∏ i, rowSum P i) = dittertConstant m * endpointRowProduct P := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  simp only [dittertConstant, endpointRowProduct]
  field_simp

/-- A contender with equal columns is the uniform board, without a
positive-entry assumption or a rigidity premise for the transpose. -/
theorem endpoint_equal_columns_contender_uniform {m n : ℕ} (hm : 2 ≤ m) (hn : 0 < n)
    (P : Board m n) (hP : IsProbability P)
    (hc : ∀ i a b, P i a = P i b)
    (hcont : separationProbability (uniformBoard m n) m ≤ separationProbability P m) :
    P = uniformBoard m n := by
  have hmpos : 0 < m := by omega
  have hF := endpoint_equal_columns_separation hn P hP hc
  rw [endpoint_factorial_rowProduct hmpos] at hF
  have hU := separationProbability_uniform (k := m) hmpos hn
  rw [uniformSeparationValue_rectangular_endpoint] at hU
  have hb := distinctUniformProbability_lt_one (k := m) hn hm
  have ha := endpoint_a_pos hmpos
  have hR := endpointRowProduct_le_one hm hP
  have hprod : endpointRowProduct P = 1 := by
    rw [hF, hU] at hcont
    have hcoeff : 0 < dittertConstant m * (1 - distinctUniformProbability n m) :=
      mul_pos ha (sub_pos.mpr hb)
    nlinarith
  rw [endpointRowProduct_eq_normalized] at hprod
  have hr := (normalizedElementarySuccess_eq_one_iff
    (rowSum_nonneg hP.1) hP.2 hm le_rfl).mp hprod
  ext i j
  rw [endpoint_equal_columns_entries hn P hc, hr]
  simp only [uniformBoard]
  ring

/-- One-sided global-maximizer rigidity suffices at sample size m. -/
theorem uniform_maximizer_endpoint_of_column_rigidity {m n : ℕ}
    (hm : 2 ≤ m) (hn : 0 < n)
    (hcol : ∀ P : Board m n, IsProbability P →
      (∀ Q : Board m n, IsProbability Q → separationProbability Q m ≤ separationProbability P m) →
      ∀ i a b, P i a = P i b) : UniformMaximizer m n m := by
  apply uniform_maximizer_of_unique_global (by omega) hn m
  intro P hP hmax
  exact endpoint_equal_columns_contender_uniform hm hn P hP (hcol P hP hmax)
    (hmax _ (uniformBoard_isProbability (by omega) hn))

end DittertRybin
