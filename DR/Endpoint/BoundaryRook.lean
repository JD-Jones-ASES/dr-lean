import DR.Endpoint.BoundaryPermanent
import DR.Endpoint.RectangularPadding
import DR.Endpoint.Normalization

/-!
# Rectangular boundary rook floor

The square permanent floor is applied to the actual padded balanced board.
The dummy-row factor is cancelled against the uniform distinct-column
probability exactly. Entrywise domination and degree-m homogeneity then
transfer the floor to any board dominating a nonnegative scaled copy.
-/

namespace DittertRybin
open scoped BigOperators

/-- Endpoint rook sums are entrywise monotone on nonnegative boards. -/
theorem endpointRookRatio_mono {m n : ℕ} {B P : Board m n}
    (hB : ∀ i j, 0 ≤ B i j) (hBP : ∀ i j, B i j ≤ P i j) :
    endpointRookRatio B ≤ endpointRookRatio P := by
  simp only [endpointRookRatio, rookSum_endpoint_eq_rowAvoidance]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold rowAvoidance
  apply Finset.sum_le_sum
  intro f _
  unfold rowAssignmentMass
  exact Finset.prod_le_prod (fun i _ => hB i (f i)) (fun i _ => hBP i (f i))

/-- Signed scalar homogeneity retains the full endpoint degree. -/
theorem endpointRookRatio_smul {m n : ℕ} (B : Board m n) (c : ℝ) :
    endpointRookRatio (c • B) = c^m * endpointRookRatio B := by
  simp only [endpointRookRatio, rookSum_endpoint_eq_rowAvoidance, rowAvoidance,
    rowAssignmentMass, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  ring

/-- The dummy-row coefficient times the uniform avoidance factor is exactly gamma_n. -/
theorem rectangularPadding_factor_mul_uniform {m n : ℕ} (hmn : m ≤ n) :
    ((n-m).factorial : ℝ) / (n : ℝ)^(n-m) * distinctUniformProbability n m =
      dittertConstant n := by
  have hfac : ((n-m).factorial : ℝ) * (n.descFactorial m : ℝ) = (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_mul_descFactorial hmn
  rw [distinctUniformProbability, div_mul_div_comm, hfac, ← pow_add,
    Nat.sub_add_cancel hmn, dittertConstant]

/-- The actual padding formula in normalized endpoint notation, still for signed inputs. -/
theorem permanent_rectangularPadding_eq_endpointRookRatio {m n : ℕ} (hmn : m ≤ n)
    (B : Board m n) :
    (rectangularPadding hmn B).permanent =
      ((n-m).factorial : ℝ) / (n : ℝ)^(n-m) * endpointRookRatio B := by
  rw [permanent_rectangularPadding]
  unfold endpointRookRatio
  ring

/-- Every balanced rectangular boundary board inherits the square one-zero floor. -/
theorem endpointRookRatio_boundary_lower_bound {m n : ℕ} (hm : 0 < m)
    (hn : 3 ≤ n) (hmn : m ≤ n) {B : Board m n}
    (hB : ∀ i j, 0 ≤ B i j)
    (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (hz : ∃ i j, B i j = 0) :
    distinctUniformProbability n m * boundaryPermanentRatio n ≤ endpointRookRatio B := by
  have hn0 : 0 < n := by omega
  have hp := permanent_boundary_lower_bound hn
    (rectangularPadding_mem_doublyStochastic hmn hm hn0 B hB hr hc)
    (rectangularPadding_hasZero hmn B hz)
  rw [permanent_rectangularPadding_eq_endpointRookRatio] at hp
  have hfactor : 0 < ((n-m).factorial : ℝ) / (n : ℝ)^(n-m) := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hf : (0 : ℝ) < (n-m).factorial := by exact_mod_cast Nat.factorial_pos (n-m)
    positivity
  apply (mul_le_mul_iff_right₀ hfactor).mp
  calc
    ((n-m).factorial : ℝ) / (n : ℝ)^(n-m) *
        (distinctUniformProbability n m * boundaryPermanentRatio n) =
        boundaryPermanentFloor n := by
      rw [← mul_assoc, rectangularPadding_factor_mul_uniform hmn, boundaryPermanentRatio]
      exact mul_div_cancel₀ _ (endpoint_a_pos hn0).ne'
    _ ≤ ((n-m).factorial : ℝ) / (n : ℝ)^(n-m) * endpointRookRatio B := hp

/-- A nonnegative scaled balanced boundary board can be transferred by entrywise domination.
No probability or positivity assumption is imposed on the dominating board. -/
theorem endpointRookRatio_boundary_lower_bound_of_smul_le {m n : ℕ}
    (hm : 0 < m) (hn : 3 ≤ n) (hmn : m ≤ n) {B P : Board m n} {c : ℝ}
    (hB : ∀ i j, 0 ≤ B i j)
    (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (hz : ∃ i j, B i j = 0) (hc0 : 0 ≤ c)
    (hdom : ∀ i j, c * B i j ≤ P i j) :
    c^m * distinctUniformProbability n m * boundaryPermanentRatio n ≤ endpointRookRatio P := by
  have hfloor := endpointRookRatio_boundary_lower_bound hm hn hmn hB hr hc hz
  have hmono : endpointRookRatio (c • B) ≤ endpointRookRatio P :=
    endpointRookRatio_mono (fun i j => mul_nonneg hc0 (hB i j)) hdom
  rw [endpointRookRatio_smul] at hmono
  have hscaled : c^m * distinctUniformProbability n m * boundaryPermanentRatio n ≤
      c^m * endpointRookRatio B := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfloor (pow_nonneg hc0 m)
  exact hscaled.trans hmono

/-- The deletion/transport parameter form, retaining t=1 and permitting any t≤1. -/
theorem endpointRookRatio_boundary_lower_bound_of_scaled_le {m n : ℕ}
    (hm : 0 < m) (hn : 3 ≤ n) (hmn : m ≤ n) {B P : Board m n} {t : ℝ}
    (hB : ∀ i j, 0 ≤ B i j)
    (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (hz : ∃ i j, B i j = 0) (ht : t ≤ 1)
    (hdom : ∀ i j, (1-t) * B i j ≤ P i j) :
    (1-t)^m * distinctUniformProbability n m * boundaryPermanentRatio n ≤ endpointRookRatio P :=
  endpointRookRatio_boundary_lower_bound_of_smul_le hm hn hmn hB hr hc hz
    (sub_nonneg.mpr ht) hdom

/-- A positive scaling transfers a zero of the dominating board to the balanced board. -/
theorem endpointRookRatio_boundary_lower_bound_of_boundary_domination {m n : ℕ}
    (hm : 0 < m) (hn : 3 ≤ n) (hmn : m ≤ n) {B P : Board m n} {t : ℝ}
    (hB : ∀ i j, 0 ≤ B i j)
    (hr : ∀ i, rowSum B i = 1/(m : ℝ))
    (hc : ∀ j, colSum B j = 1/(n : ℝ))
    (hzP : ∃ i j, P i j = 0) (ht : t < 1)
    (hdom : ∀ i j, (1-t) * B i j ≤ P i j) :
    (1-t)^m * distinctUniformProbability n m * boundaryPermanentRatio n ≤ endpointRookRatio P := by
  have hzB : ∃ i j, B i j = 0 := by
    obtain ⟨i, j, hz⟩ := hzP
    refine ⟨i, j, le_antisymm ?_ (hB i j)⟩
    have h := hdom i j
    rw [hz] at h
    by_contra hnot
    exact (not_lt_of_ge h) (mul_pos (sub_pos.mpr ht) (lt_of_not_ge hnot))
  exact endpointRookRatio_boundary_lower_bound_of_scaled_le hm hn hmn hB hr hc hzB ht.le hdom

end DittertRybin
