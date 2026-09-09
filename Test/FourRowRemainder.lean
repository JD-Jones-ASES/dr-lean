import DR.Rectangular.FourRowLeadingConcentration

/-! Actual sampling normalization, signed finite identities, and closed-simplex boundaries. -/

open DittertRybin DittertRybin.Certificates
open scoped BigOperators

private theorem uniform_four_leading :
    6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum (uniformBoard 4 4)))
      (fun i => uniformBoard 4 4 i j)) = (87 / 64 : ℝ) := by
  have hr : rowSum (uniformBoard 4 4) = fun _ => (1/4 : ℝ) := by
    funext i
    norm_num [rowSum, uniformBoard]
  rw [hr]
  simp_rw [fourRowLeadingKernel_quadratic (fun _ => (1/4 : ℝ)) _ (by intro i; norm_num)]
  norm_num [fourRowReferenceQuadratic, uniformBoard]

private theorem uniform_four_excess :
    fourRowRestrictedCollisionExcess (uniformBoard 4 4) = (551 / 1024 : ℝ) := by
  rw [fourRowRestrictedCollisionExcess_eq _ (uniformBoard_isProbability (by decide) (by decide)),
    uniform_four_leading, fourRow_failure_uniform (by decide)]
  norm_num

-- Row-failure restriction strictly decreases the unrestricted column correction.
example : fourRowRestrictedCollisionExcess (uniformBoard 4 4) <
    fourSampleCollisionExcess (colSum (uniformBoard 4 4)) := by
  rw [uniform_four_excess, fourSampleCollisionExcess_formula]
  norm_num [colSum, uniformBoard, Fin.sum_univ_four]

-- A missing or halved pair-count factor does not satisfy the exact actual leading identity.
example : ¬ (6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum (uniformBoard 4 4)))
      (fun i => uniformBoard 4 4 i j)) = (87 / 128 : ℝ)) := by
  rw [uniform_four_leading]
  norm_num

-- Fixed-row integration is an identity even on negative unnormalized weights.
example : (∑ c : Fin 4 → Fin 1, if c 0 = c 1 then ∏ _t : Fin 4, (-2 : ℝ) else 0) = 16 := by
  have h := fourRow_fixed_rows_equal_columns (fun _ : Fin 4 => fun _ : Fin 1 => (-2 : ℝ))
    (fun _ => 0)
  convert h using 1
  norm_num [rowSum]

-- An empty column type still satisfies the signed row-distinct identity.
example : eventMass (fun _a : Fin 4 × Fin 0 => (7 : ℝ))
    {s : Fin 4 → Fin 4 × Fin 0 | RowsDistinct s ∧ (s 0).2 = (s 1).2} = 0 := by
  have h := fourRow_equal_pair_rows_distinct_mass (fun _ : Fin 4 => fun _ : Fin 0 => (7 : ℝ))
  simpa using h

-- No dimension threshold or positive-entry hypothesis is needed for the remainder.
example {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    0 ≤ 6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
        (1 - separationProbability P 4) ∧
      6 * (∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j)) -
        (1 - separationProbability P 4) ≤ 11 * (∑ j, colSum P j ^ 3) :=
  fourRow_leading_collision_remainder P hP

private noncomputable def zeroColumnBoard : Board 4 2 := fun _ j => if j = 0 then 1/4 else 0

private theorem zeroColumnBoard_probability : IsProbability zeroColumnBoard := by
  constructor
  · intro i j; unfold zeroColumnBoard; split <;> norm_num
  · norm_num [totalMass, rowSum, zeroColumnBoard, Fin.sum_univ_succ]

example : fourRowRestrictedCollisionExcess zeroColumnBoard ≤ 5 := by
  have h := (fourRowRestrictedCollisionExcess_bounds _ zeroColumnBoard_probability).2
  rw [fourSampleCollisionExcess_formula] at h
  norm_num [colSum, zeroColumnBoard, Fin.sum_univ_succ] at h
  exact h

-- The two completed inputs are no longer hypotheses of the strict sampling consequence.
example {n : ℕ} (hn : 500 ≤ n) (P : Board 4 n) (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (hminor : ∀ j, fourRowGaugeColumn P j ^ 2 ≤
      quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j))
    (a b : Fin n) (hab : a ≠ b) (hdiff : ∃ i, P i a ≠ P i b) :
    separationProbability P 4 < separationProbability (blendColumns P a b (1/2)) 4 := by
  obtain ⟨hm, hα, hν⟩ := fourRow_contender_deletion_of_minorant hn P hP hcont hminor a b hab
  exact fourRow_separationProbability_blend_strict P hP.1 a b hab (1/2)
    (by norm_num) (by norm_num) hdiff hm hα hν

#print axioms fourRow_column_observable
#print axioms fourRow_injective_pair_sum
#print axioms fourRow_equal_pair_row_failure_mass
#print axioms fourRow_row_failure_pair_sum
#print axioms fourRow_leading_collision_remainder_polynomial
#print axioms fourRow_leading_collision_remainder
#print axioms fourRow_contender_deletion_of_minorant
