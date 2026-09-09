import DR.Rectangular.FourRowLeadingCollisionFinite

/-!
# The actual row-failure leading collision moment

A fixed equal-column pair is integrated exactly. Its row-distinct part
counts the two orders of the complementary rows; subtracting it leaves the
polynomial B_4 quadratic. Sample permutation symmetry supplies all six pairs.
-/

namespace DittertRybin

open scoped BigOperators
open Classical Certificates

theorem fourRowLeadingKernel_eq_complement (r : Fin 4 → ℝ) (i h : Fin 4) :
    fourRowLeadingKernel r i h = 1 - 2 * fourRowColumnComplement r i h := by
  by_cases hi : i = h <;> simp [fourRowLeadingKernel, fourRowColumnComplement, hi]

theorem fourRowLeadingKernel_quadratic_complement (r x : Fin 4 → ℝ) :
    quadraticValue (fourRowLeadingKernel r) x = (∑ i, x i) ^ 2 -
      2 * ∑ i, ∑ h, x i * fourRowColumnComplement r i h * x h := by
  have ht (i h : Fin 4) : x i * fourRowLeadingKernel r i h * x h =
      x i * x h - 2 * (x i * fourRowColumnComplement r i h * x h) := by
    rw [fourRowLeadingKernel_eq_complement]
    ring
  simp only [quadraticValue, ht, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, pow_two]

/-- The row-distinct contribution of a fixed equal-column pair, on arbitrary real boards. -/
theorem fourRow_equal_pair_rows_distinct_mass {n : ℕ} (P : Board 4 n) :
    eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
      {s : Fin 4 → Fin 4 × Fin n | RowsDistinct s ∧ (s 0).2 = (s 1).2} =
      2 * ∑ j, ∑ i, ∑ h, P i j * fourRowColumnComplement (rowSum P) i h * P h j := by
  unfold eventMass
  calc
    _ = ∑ q : (Fin 4 → Fin 4) × (Fin 4 → Fin n),
        if Function.Injective q.1 ∧ q.2 0 = q.2 1 then ∏ t, P (q.1 t) (q.2 t) else 0 := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow (Fin 4) (fun _ => Fin 4) (fun _ => Fin n))
      intro s
      by_cases hr : Function.Injective (fun t => (s t).1) <;>
        by_cases hc : (s 0).2 = (s 1).2 <;>
        simp [Equiv.arrowProdEquivProdArrow, RowsDistinct, sampleMass, hr, hc]
    _ = ∑ r : Fin 4 → Fin 4, ∑ c : Fin 4 → Fin n,
        if Function.Injective r ∧ c 0 = c 1 then ∏ t, P (r t) (c t) else 0 := by
      exact Fintype.sum_prod_type _
    _ = ∑ r : Fin 4 → Fin 4, ∑ j,
        if Function.Injective r then P (r 0) j * P (r 1) j * rowSum P (r 2) * rowSum P (r 3) else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : Function.Injective r
      · simp only [hr, true_and, if_true]
        rw [fourRow_fixed_rows_equal_columns]
        simp only [Finset.sum_mul]
      · simp [hr]
    _ = _ := by
      rw [Finset.sum_comm]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact fourRow_injective_pair_sum (rowSum P) (fun i => P i j)

/-- A fixed equal-column pair has its genuine column second moment under iid sampling. -/
theorem fourRow_equal_pair_mass {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
      {s : Fin 4 → Fin 4 × Fin n | (s 0).2 = (s 1).2} = ∑ j, colSum P j ^ 2 := by
  have hc : (∑ j, colSum P j) = 1 := (totalMass_eq_sum_colSum P).symm.trans hP.2
  let e : Fin 2 ↪ Fin 4 := sampleIndexPairEmbedding ⟨(0,1), by decide⟩
  have h := eventMass_restrict (colSum P) hc e {s : Fin 2 → Fin n | s 0 = s 1}
  rw [eventMass_two_equal] at h
  exact (fourRow_eventMass_columns P {s : Fin 4 → Fin n | s 0 = s 1}).trans h

/-- The fixed pair restricted to row failure is exactly the sum of B_4 column quadratics. -/
theorem fourRow_equal_pair_row_failure_mass {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
      {s : Fin 4 → Fin 4 × Fin n | ¬ RowsDistinct s ∧ (s 0).2 = (s 1).2} =
      ∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j) := by
  have hsplit : eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
        {s : Fin 4 → Fin 4 × Fin n | (s 0).2 = (s 1).2} =
      eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
        {s : Fin 4 → Fin 4 × Fin n | RowsDistinct s ∧ (s 0).2 = (s 1).2} +
      eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
        {s : Fin 4 → Fin 4 × Fin n | ¬ RowsDistinct s ∧ (s 0).2 = (s 1).2} := by
    simp only [eventMass, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    by_cases hr : RowsDistinct s <;> by_cases hc : (s 0).2 = (s 1).2 <;> simp [hr,hc]
  rw [fourRow_equal_pair_mass P hP, fourRow_equal_pair_rows_distinct_mass] at hsplit
  simp only [fourRowLeadingKernel_quadratic_complement, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp only [colSum] at hsplit
  linarith

/-- The fixed-pair formula is independent of the two distinct sample indices. -/
theorem fourRow_any_pair_row_failure_mass {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (ij : SampleIndexPair 4) :
    eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
      {s : Fin 4 → Fin 4 × Fin n | ¬ RowsDistinct s ∧ (s ij.val.1).2 = (s ij.val.2).2} =
      ∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j) := by
  let e0 : Fin 2 ↪ Fin 4 := sampleIndexPairEmbedding ⟨(0,1), by decide⟩
  let e := sampleIndexPairEmbedding ij
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair e0 e e0.injective e.injective
  have h0 : σ 0 = ij.val.1 := hσ 0
  have h1 : σ 1 = ij.val.2 := hσ 1
  have h := eventMass_permute (fun a : Fin 4 × Fin n => P a.1 a.2) σ
    {s : Fin 4 → Fin 4 × Fin n | ¬ RowsDistinct s ∧ (s 0).2 = (s 1).2}
  simp only [Set.mem_ofPred_eq, rowsDistinct_permute, Function.comp_apply, h0,h1] at h
  exact h.trans (fourRow_equal_pair_row_failure_mass P hP)

/-- Summing the six actual collision pairs gives the factor-six leading kernel moment. -/
theorem fourRow_row_failure_pair_sum {n : ℕ} (P : Board 4 n) (hP : IsProbability P) :
    (∑ ij : SampleIndexPair 4, eventMass (fun a : Fin 4 × Fin n => P a.1 a.2)
      {s : Fin 4 → Fin 4 × Fin n | ¬ RowsDistinct s ∧ (s ij.val.1).2 = (s ij.val.2).2}) =
      6 * ∑ j, quadraticValue (fourRowLeadingKernel (rowSum P)) (fun i => P i j) := by
  simp_rw [fourRow_any_pair_row_failure_mass P hP]
  norm_num [card_sampleIndexPair, Nat.choose]

end DittertRybin
