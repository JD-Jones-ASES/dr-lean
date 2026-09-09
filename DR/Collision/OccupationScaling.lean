import DR.ProbabilityScaling
import DR.Collision.Deletion

/-!
# Conditional occupation is unchanged by nonzero scaling

Both the event numerator and the conditioning denominator have degree k.
Their common factor cancels, even when the conditioning mass is zero under
Lean's total division convention. Probability applications separately prove
that the conditioning mass is positive.
-/

namespace DittertRybin

theorem columnDistinctMass_smul {m n : ℕ} (P : Board m n) (k : ℕ) (c : ℝ) :
    columnDistinctMass (c • P) k = c ^ k * columnDistinctMass P k := by
  exact eventMass_mul (fun a : Fin m × Fin n => P a.1 a.2) c _

theorem columnConditionedWeight_smul {m n : ℕ} (P : Board m n) (k : ℕ)
    (c : ℝ) (hc : c ≠ 0) (s : Fin k → Fin m × Fin n) :
    columnConditionedWeight (c • P) k s = columnConditionedWeight P k s := by
  classical
  unfold columnConditionedWeight
  rw [columnDistinctMass_smul]
  by_cases hs : ColsDistinct s
  · simp only [if_pos hs]
    change sampleMass (fun a : Fin m × Fin n => c * P a.1 a.2) s /
      (c ^ k * columnDistinctMass P k) = _
    rw [sampleMass_mul, mul_div_mul_left _ _ (pow_ne_zero k hc)]
  · simp [hs]

theorem columnConditionalExpectation_smul {m n : ℕ} (P : Board m n) (k : ℕ)
    (c : ℝ) (hc : c ≠ 0) (f : (Fin k → Fin m × Fin n) → ℝ) :
    columnConditionalExpectation (c • P) k f = columnConditionalExpectation P k f := by
  simp only [columnConditionalExpectation, columnConditionedWeight_smul P k c hc]

theorem conditionalRowsProbability_smul {m n : ℕ} (P : Board m n) (k : ℕ)
    (c : ℝ) (hc : c ≠ 0) :
    conditionalRowsProbability (c • P) k = conditionalRowsProbability P k :=
  columnConditionalExpectation_smul P k c hc _

theorem occupationProbability_smul {m n : ℕ} (P : Board m n) (k : ℕ)
    (c : ℝ) (hc : c ≠ 0) (i : Fin m) :
    occupationProbability (c • P) k i = occupationProbability P k i :=
  columnConditionalExpectation_smul P k c hc _

theorem conditionalRowsAbsent_smul {m n : ℕ} (P : Board m n) (k : ℕ)
    (c : ℝ) (hc : c ≠ 0) (i h : Fin m) :
    conditionalRowsAbsent (c • P) k i h = conditionalRowsAbsent P k i h :=
  columnConditionalExpectation_smul P k c hc _

theorem occupationKernel_smul {m n : ℕ} (P : Board m n) (k : ℕ)
    (c : ℝ) (hc : c ≠ 0) (i h : Fin m) :
    occupationKernel (c • P) k i h = occupationKernel P k i h := by
  simp only [occupationKernel, conditionalRowsAbsent_smul P k c hc]

theorem normalizeBoard_eq_smul {m n : ℕ} (P : Board m n) :
    normalizeBoard P = (totalMass P)⁻¹ • P := by
  ext i j
  simp [normalizeBoard, div_eq_mul_inv, mul_comm]

theorem occupationKernel_normalizeBoard {m n : ℕ} (P : Board m n) (k : ℕ)
    (hμ : totalMass P ≠ 0) (i h : Fin m) :
    occupationKernel (normalizeBoard P) k i h = occupationKernel P k i h := by
  rw [normalizeBoard_eq_smul]
  exact occupationKernel_smul P k _ (inv_ne_zero hμ) i h

end DittertRybin
