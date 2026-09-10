import DR.Endpoint.NearEndpointPaddingCounting
import DR.Endpoint.NearEndpointNormalization
import DR.Endpoint.BoundaryPermanent

/-! The actual n+1 square padding for n−1 draws. The new corner is zero;
the one-zero boundary floor, not the uniform square permanent, is its
normalizing reference. -/
namespace DittertRybin
open scoped BigOperators
open Matrix

/-- A new first row/column with border1/n, corner zero, and core(n−1)P. -/
noncomputable def nearEndpointPadding {n : ℕ} (P : Board n n) : Board (n+1) (n+1) :=
  cornerZeroBorder P ((n-1 : ℕ) : ℝ) (1/(n : ℝ)) (1/(n : ℝ))

@[simp] theorem nearEndpointPadding_corner {n : ℕ} (P : Board n n) :
    nearEndpointPadding P 0 0 = 0 := rfl

@[simp] theorem nearEndpointPadding_original {n : ℕ} (P : Board n n) (i j : Fin n) :
    nearEndpointPadding P i.succ j.succ = (n-1 : ℕ)*P i j := rfl

/-- The original boundary zero and the new zero have distinct rows and columns. -/
theorem nearEndpointPadding_two_independent_zeros {n : ℕ} {P : Board n n}
    (hz : ∃ i j, P i j = 0) :
    ∃ i₁ i₂ j₁ j₂, i₁ ≠ i₂ ∧ j₁ ≠ j₂ ∧
      nearEndpointPadding P i₁ j₁ = 0 ∧ nearEndpointPadding P i₂ j₂ = 0 := by
  obtain ⟨i,j,hz⟩ := hz
  refine ⟨0,i.succ,0,j.succ,Fin.succ_ne_zero i |>.symm,
    Fin.succ_ne_zero j |>.symm,rfl,?_⟩
  simp [hz]

/-- Exact signed rook/permanent bridge, with all dummy factors explicit. -/
theorem permanent_nearEndpointPadding {n : ℕ} (hn : 0 < n) (P : Board n n) :
    (nearEndpointPadding P).permanent =
      ((n-1 : ℕ) : ℝ)^(n-1)/(n : ℝ)^2 * rookSum P (n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_eq_add_one] at *
  rw [nearEndpointPadding, permanent_cornerZeroBorder]
  simp only [Nat.add_sub_cancel]
  ring

/-- The padding is doubly stochastic for every balanced nonnegative input,
including the one-cell case. -/
theorem nearEndpointPadding_mem_doublyStochastic {n : ℕ} (hn : 0 < n)
    {P : Board n n} (hP : ∀ i j, 0 ≤ P i j)
    (hr : ∀ i, rowSum P i = 1/(n : ℝ))
    (hc : ∀ j, colSum P j = 1/(n : ℝ)) :
    nearEndpointPadding P ∈ doublyStochastic ℝ (Fin (n+1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply mem_doublyStochastic_iff_sum.mpr
  refine ⟨?_,?_,?_⟩
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases <;>
      simp only [nearEndpointPadding, cornerZeroBorder_zero_zero,
        cornerZeroBorder_zero_succ, cornerZeroBorder_succ_zero, cornerZeroBorder_succ_succ]
    · rfl
    · positivity
    · positivity
    · exact mul_nonneg (Nat.cast_nonneg _) (hP _ _)
  · intro i
    cases i using Fin.cases with
    | zero => simp [nearEndpointPadding, Fin.sum_univ_succ, hn0]
    | succ i =>
      simp only [nearEndpointPadding, Fin.sum_univ_succ, cornerZeroBorder_succ_zero,
        cornerZeroBorder_succ_succ, ← Finset.mul_sum]
      rw [show (∑ j, P i j) = 1/(n : ℝ) from hr i, Nat.cast_sub hn]
      push_cast
      field_simp
      ring
  · intro j
    cases j using Fin.cases with
    | zero => simp [nearEndpointPadding, Fin.sum_univ_succ, hn0]
    | succ j =>
      simp only [nearEndpointPadding, Fin.sum_univ_succ, cornerZeroBorder_zero_succ,
        cornerZeroBorder_succ_succ, ← Finset.mul_sum]
      rw [show (∑ i, P i j) = 1/(n : ℝ) from hc j, Nat.cast_sub hn]
      push_cast
      field_simp
      ring

/-- For n−1 samples the uniform marginal factor is n*gamma_n. -/
theorem distinctUniformProbability_pred {n : ℕ} (hn : 0 < n) :
    distinctUniformProbability n (n-1) = (n : ℝ)*dittertConstant n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_eq_add_one] at *
  have hd : (k+1).descFactorial k = (k+1).factorial := by
    rw [Nat.descFactorial_eq_div (by omega)]
    simp
  simp only [distinctUniformProbability, Nat.add_sub_cancel, hd, dittertConstant,
    pow_succ, Nat.cast_add, Nat.cast_one]
  have hx : (k : ℝ)+1 ≠ 0 := by positivity
  field_simp

/-- The permanent is normalized by the one-zero boundary floor of order n+1.
This retains both collision-avoidance factors from the source formula. -/
theorem permanent_nearEndpointPadding_eq_ratio {n : ℕ} (hn : 0 < n) (P : Board n n) :
    (nearEndpointPadding P).permanent =
      boundaryPermanentFloor (n+1)/distinctUniformProbability n (n-1)*nearEndpointRookRatio P := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  simp only [Nat.succ_eq_add_one] at *
  have hd : (k+1).descFactorial k = (k+1).factorial := by
    rw [Nat.descFactorial_eq_div (by omega)]
    simp
  have hx : (k : ℝ)+1 ≠ 0 := by positivity
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  rw [permanent_nearEndpointPadding (by omega), boundaryPermanentFloor_succ_succ]
  simp only [nearEndpointRookRatio, Nat.add_sub_cancel, distinctUniformProbability, hd,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, div_pow]
  field_simp
  ring_nf
  rw [show (1+(k : ℝ)*2+k^2) = (1+(k : ℝ))^2 by ring, ← pow_mul, Nat.mul_comm]

/-- Uniform probability input produces the sharp one-zero boundary value. -/
theorem permanent_nearEndpointPadding_uniform {n : ℕ} (hn : 0 < n) :
    (nearEndpointPadding (uniformBoard n n)).permanent = boundaryPermanentFloor (n+1) := by
  rw [permanent_nearEndpointPadding_eq_ratio hn, nearEndpointRookRatio_uniform hn]
  exact div_mul_cancel₀ _ (distinctUniformProbability_pos hn (Nat.sub_le n 1)).ne'

end DittertRybin
