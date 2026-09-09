import DR.Rectangular.FourRowLeadingCollision
import DR.Rectangular.FourRowColumnCollision

/-!
# The actual leading-collision remainder on four rows

The nonnegative excess of the equal-column-pair count over its union
indicator can only decrease when restricted to row failure. Exact outcome
marginalization then bounds it by the unrestricted column correction.
-/

namespace DittertRybin

open scoped BigOperators
open Classical Certificates

private theorem colsDistinct_indicator_eq {n : ℕ} (s : Fin 4 → Fin 4 × Fin n) :
    (if ColsDistinct s then (0 : ℝ) else 1) =
      (if Function.Injective (fun t => (s t).2) then 0 else 1) := by
  by_cases h : ColsDistinct s
  · rw [if_pos h, if_pos (show Function.Injective (fun t => (s t).2) from h)]
  · rw [if_neg h, if_neg (show ¬ Function.Injective (fun t => (s t).2) from h)]

noncomputable def fourRowRestrictedCollisionExcess {n : ℕ} (P : Board 4 n) : ℝ :=
  ∑ s : Fin 4 → Fin 4 × Fin n, sampleMass (fun a => P a.1 a.2) s *
    (if RowsDistinct s then 0 else
      fourSampleEqualPairCount (fun t => (s t).2) - if ColsDistinct s then 0 else 1)

/-- The factor-six polynomial is the actual equal-pair count restricted to row failure. -/
theorem fourRow_leading_collision_observable {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) =
      ∑ s : Fin 4 → Fin 4 × Fin n, sampleMass (fun a => P a.1 a.2) s *
        (if RowsDistinct s then 0 else fourSampleEqualPairCount (fun t => (s t).2)) := by
  rw [← fourRow_row_failure_pair_sum P hP]
  simp only [eventMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hr : RowsDistinct s
  · simp [hr]
  · simp only [fourSampleEqualPairCount, Finset.mul_sum, Set.mem_ofPred_eq, hr,
      not_false_eq_true, true_and, if_false, mul_ite, mul_one, mul_zero]

theorem fourRow_failure_event_mass {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
      {s : Fin 4 → Fin 4 × Fin n | ¬ (RowsDistinct s ∨ ColsDistinct s)} =
      1 - separationProbability P 4 :=
  eventMass_compl _ ((sum_cell_weights P).trans hP.2) _

/-- The restricted excess is exactly the leading moment minus the original failure probability. -/
theorem fourRowRestrictedCollisionExcess_eq {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    fourRowRestrictedCollisionExcess P =
      6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
        (1 - separationProbability P 4) := by
  rw [fourRow_leading_collision_observable P hP, ← fourRow_failure_event_mass P hP]
  simp only [fourRowRestrictedCollisionExcess, eventMass, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hr : RowsDistinct s <;> by_cases hc : ColsDistinct s <;>
    simp [hr,hc, mul_sub]

/-- Restricting a nonnegative collision excess to row failure decreases its mass. -/
theorem fourRowRestrictedCollisionExcess_bounds {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    0 ≤ fourRowRestrictedCollisionExcess P ∧
      fourRowRestrictedCollisionExcess P ≤ fourSampleCollisionExcess (colSum P) := by
  have hpoint (s : Fin 4 → Fin 4 × Fin n) :
      0 ≤ fourSampleEqualPairCount (fun t => (s t).2) - if ColsDistinct s then 0 else 1 := by
    rw [colsDistinct_indicator_eq]
    exact fourSample_collision_excess_nonneg (fun t => (s t).2)
  have hmass (s : Fin 4 → Fin 4 × Fin n) : 0 ≤ sampleMass (fun a => P a.1 a.2) s :=
    sampleMass_nonneg _ (fun a => hP.1 a.1 a.2) s
  constructor
  · apply Finset.sum_nonneg
    intro s _
    apply mul_nonneg (hmass s)
    by_cases hr : RowsDistinct s
    · simp only [hr, if_true, le_refl]
    · simpa only [hr, if_false] using hpoint s
  · calc
      _ ≤ ∑ s : Fin 4 → Fin 4 × Fin n, sampleMass (fun a => P a.1 a.2) s *
          (fourSampleEqualPairCount (fun t => (s t).2) - if ColsDistinct s then 0 else 1) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (hmass s)
        by_cases hr : RowsDistinct s
        · simpa only [hr, if_true] using hpoint s
        · simp only [hr, if_false, le_refl]
      _ = _ := by
        simp_rw [colsDistinct_indicator_eq]
        exact
          fourRow_column_observable P (fun c =>
            fourSampleEqualPairCount c - if Function.Injective c then 0 else 1)

/-- The exact unrestricted column correction bounds the actual restricted remainder. -/
theorem fourRow_leading_collision_remainder_polynomial {n : ℕ} (P : Board 4 n)
    (hP : IsProbability P) :
    0 ≤ 6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
        (1 - separationProbability P 4) ∧
      6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
        (1 - separationProbability P 4) ≤
          8 * (∑ j, colSum P j ^ 3) + 3 * (∑ j, colSum P j ^ 2) ^ 2 -
            6 * (∑ j, colSum P j ^ 4) := by
  rw [← fourRowRestrictedCollisionExcess_eq P hP]
  have h := fourRowRestrictedCollisionExcess_bounds P hP
  rw [fourSampleCollisionExcess_formula,
    (totalMass_eq_sum_colSum P).symm.trans hP.2, mul_one] at h
  exact h

/-- The complete actual remainder estimate, on the full closed probability simplex. -/
theorem fourRow_leading_collision_remainder {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    0 ≤ 6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
        (1 - separationProbability P 4) ∧
      6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
        (1 - separationProbability P 4) ≤ 11 * (∑ j, colSum P j ^ 3) := by
  rw [← fourRowRestrictedCollisionExcess_eq P hP]
  obtain ⟨h0, h1⟩ := fourRowRestrictedCollisionExcess_bounds P hP
  have hc := fourSampleCollisionExcess_bounds (colSum P) (colSum_nonneg hP.1)
    ((totalMass_eq_sum_colSum P).symm.trans hP.2)
  exact ⟨h0, h1.trans hc.2⟩

/-- The lower-failure form is the precise input to the contender concentration assembly. -/
theorem fourRow_failure_lower_of_leading {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
      11 * (∑ j, colSum P j ^ 3) ≤ 1 - separationProbability P 4 := by
  have h := (fourRow_leading_collision_remainder P hP).2
  linarith

end DittertRybin
