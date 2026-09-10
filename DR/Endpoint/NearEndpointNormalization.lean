import DR.Endpoint.Normalization

/-! Exact normalization for n−1 iid draws on an n×n board. The polynomial
identity is signed; the deficit bounds retain the full probability simplex. -/
namespace DittertRybin
open scoped BigOperators

noncomputable def nearEndpointRowRatio {n : ℕ} (P : Board n n) : ℝ :=
  normalizedElementarySuccess (rowSum P) (n-1)

noncomputable def nearEndpointColumnRatio {n : ℕ} (P : Board n n) : ℝ :=
  normalizedElementarySuccess (colSum P) (n-1)

noncomputable def nearEndpointRookRatio {n : ℕ} (P : Board n n) : ℝ :=
  ((n-1).factorial : ℝ)*rookSum P (n-1)/distinctUniformProbability n (n-1)

noncomputable def nearEndpointRookDeficit {n : ℕ} (P : Board n n) : ℝ :=
  distinctUniformProbability n (n-1)-nearEndpointRookRatio P

/-- Normalized elementary success has exactly the factorial/uniform-event
normalization, also for signed marginals. -/
theorem normalizedElementarySuccess_eq_event_ratio {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ n) (x : Fin n → ℝ) :
    normalizedElementarySuccess x k =
      (k.factorial : ℝ)*elementarySymmetric x k/distinctUniformProbability n k := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : (n.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  simp only [normalizedElementarySuccess, elementaryMean, distinctUniformProbability,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  field_simp

/-- Signed actual semimatching identity, without normalization of the board. -/
theorem separationProbability_nearEndpoint_ratios {n : ℕ} (hn : 0 < n)
    (P : Board n n) :
    separationProbability P (n-1) = distinctUniformProbability n (n-1)*
      (nearEndpointRowRatio P+nearEndpointColumnRatio P-nearEndpointRookRatio P) := by
  have ha := distinctUniformProbability_pos hn (Nat.sub_le n 1)
  rw [separationProbability_eq_rook]
  simp only [nearEndpointRowRatio, nearEndpointColumnRatio,
    normalizedElementarySuccess_eq_event_ratio hn (Nat.sub_le n 1), nearEndpointRookRatio]
  field_simp

theorem nearEndpointRookRatio_nonneg {n : ℕ} {P : Board n n}
    (hP : ∀ i j, 0 ≤ P i j) : 0 ≤ nearEndpointRookRatio P := by
  apply div_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_) (by
    unfold distinctUniformProbability; positivity)
  exact Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun c _ =>
    Finset.prod_nonneg fun i _ => hP (r i) (c i)

/-- Every rook degree is monotone on nonnegative boards, including zero cells. -/
theorem rookSum_mono {m n k : ℕ} {B P : Board m n}
    (hB : ∀ i j, 0 ≤ B i j) (hBP : ∀ i j, B i j ≤ P i j) :
    rookSum B k ≤ rookSum P k := by
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro c hc
  exact Finset.prod_le_prod (fun i _ => hB (r i) (c i)) (fun i _ => hBP (r i) (c i))

/-- The rook polynomial has its actual sample degree even for signed scalars. -/
theorem rookSum_smul {m n : ℕ} (P : Board m n) (k : ℕ) (c : ℝ) :
    rookSum (c • P) k = c^k*rookSum P k := by
  simp only [rookSum, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]

/-- A constant matrix counts each placement once, with its row-subset factor. -/
theorem rookSum_const (m n k : ℕ) (a : ℝ) :
    rookSum (fun _ : Fin m => fun _ : Fin n => a) k =
      (m.choose k : ℝ)*(n.descFactorial k : ℝ)*a^k := by
  classical
  have he := elementarySymmetric_const m k a
  simp only [elementarySymmetric, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  simp only [rookSum, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_const, Fintype.card_embedding_eq, Fintype.card_fin, nsmul_eq_mul]
  have he' : (Fintype.card (Fin k ↪o Fin m) : ℝ)*a^k = (m.choose k : ℝ)*a^k := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using he
  nlinarith [congrArg (fun z : ℝ => (n.descFactorial k : ℝ)*z) he']

theorem nearEndpointRookRatio_mono {n : ℕ} {B P : Board n n}
    (hB : ∀ i j, 0 ≤ B i j) (hBP : ∀ i j, B i j ≤ P i j) :
    nearEndpointRookRatio B ≤ nearEndpointRookRatio P := by
  apply div_le_div_of_nonneg_right _ (by unfold distinctUniformProbability; positivity)
  exact mul_le_mul_of_nonneg_left (rookSum_mono hB hBP) (Nat.cast_nonneg _)

theorem nearEndpointRookRatio_smul {n : ℕ} (P : Board n n) (c : ℝ) :
    nearEndpointRookRatio (c • P) = c^(n-1)*nearEndpointRookRatio P := by
  rw [nearEndpointRookRatio, rookSum_smul]
  unfold nearEndpointRookRatio
  ring

/-- Both marginal deficits share one actual rook deficit. Zero entries and
zero deficit are retained; no stationary-point assumption is used. -/
theorem nearEndpoint_contender_deficit_budget {n : ℕ} (hn : 3 ≤ n)
    {P : Board n n} (hP : IsProbability P)
    (hcont : uniformSeparationValue n n (n-1) ≤ separationProbability P (n-1)) :
    0 ≤ 1-nearEndpointRowRatio P ∧ 0 ≤ 1-nearEndpointColumnRatio P ∧
      (1-nearEndpointRowRatio P)+(1-nearEndpointColumnRatio P) ≤ nearEndpointRookDeficit P ∧
      0 ≤ nearEndpointRookDeficit P ∧
      nearEndpointRookDeficit P ≤ distinctUniformProbability n (n-1) := by
  have hR : nearEndpointRowRatio P ≤ 1 :=
    normalizedElementarySuccess_le_one (rowSum_nonneg hP.1) hP.2 (by omega) (Nat.sub_le n 1)
  have hS : nearEndpointColumnRatio P ≤ 1 :=
    normalizedElementarySuccess_le_one (colSum_nonneg hP.1)
      ((totalMass_eq_sum_colSum P).symm.trans hP.2) (by omega) (Nat.sub_le n 1)
  have hT := nearEndpointRookRatio_nonneg hP.1
  have ha := distinctUniformProbability_pos (by omega : 0 < n) (Nat.sub_le n 1)
  rw [separationProbability_nearEndpoint_ratios (by omega)] at hcont
  simp only [uniformSeparationValue] at hcont
  have hbudget : (1-nearEndpointRowRatio P)+(1-nearEndpointColumnRatio P) ≤
      nearEndpointRookDeficit P := by
    unfold nearEndpointRookDeficit
    nlinarith
  refine ⟨sub_nonneg.mpr hR, sub_nonneg.mpr hS, hbudget, by linarith, ?_⟩
  unfold nearEndpointRookDeficit
  linarith

/-- The uniform rook ratio equals the same marginal collision-avoidance
factor a=(n)_(n−1)/n^(n−1), rather than one. -/
theorem nearEndpointRookRatio_uniform {n : ℕ} (hn : 0 < n) :
    nearEndpointRookRatio (uniformBoard n n) = distinctUniformProbability n (n-1) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hru : rowSum (uniformBoard n n) = fun _ => 1/(n : ℝ) := by
    funext i
    simp [rowSum, uniformBoard]
    field_simp
  have hcu : colSum (uniformBoard n n) = fun _ => 1/(n : ℝ) := by
    funext j
    simp [colSum, uniformBoard]
    field_simp
  have hr : nearEndpointRowRatio (uniformBoard n n) = 1 := by
    unfold nearEndpointRowRatio
    rw [hru]
    exact normalizedElementarySuccess_uniform hn (Nat.sub_le n 1)
  have hc : nearEndpointColumnRatio (uniformBoard n n) = 1 := by
    unfold nearEndpointColumnRatio
    rw [hcu]
    exact normalizedElementarySuccess_uniform hn (Nat.sub_le n 1)
  have h := separationProbability_nearEndpoint_ratios hn (uniformBoard n n)
  rw [separationProbability_uniform hn hn, hr, hc] at h
  simp only [uniformSeparationValue] at h
  have ha := distinctUniformProbability_pos hn (Nat.sub_le n 1)
  nlinarith

end DittertRybin
