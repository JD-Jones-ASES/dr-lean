import DR.Rectangular.FourRowAveraging
import DR.Collision.FirstMoment

/-!
# Initial concentration from the actual four-sample contender condition

No leading-kernel minorant is used here. A coincident pair of sampled cells
already forces failure. Comparison with the exact uniform failure value
therefore bounds every column mass on the full closed probability simplex.
-/

namespace DittertRybin

open scoped BigOperators

/-- A fixed coincident pair is an actual failure event. -/
theorem fourRow_cellSquareSum_le_failure {m n : ℕ} {P : Board m n}
    (hP : IsProbability P) : cellSquareSum P ≤ 1 - separationProbability P 4 := by
  let ij : SampleIndexPair 4 := ⟨(0,1), by decide⟩
  rw [← collisionEvent_mass_of_same_pair hP ij, ← collision_union_mass hP]
  apply eventMass_mono (fun a : Fin m × Fin n => P a.1 a.2) (fun a => hP.1 a.1 a.2)
  intro s hs
  exact ⟨(ij,ij), hs⟩

/-- Exact uniform failure, retaining the negative second-order term. -/
theorem fourRow_failure_uniform {n : ℕ} (hn : 4 ≤ n) :
    1 - separationProbability (uniformBoard 4 n) 4 =
      (29 / 32 : ℝ) * (6 / n - 11 / (n : ℝ) ^ 2 + 6 / (n : ℝ) ^ 3) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  rw [separationProbability_uniform (by decide) (by omega)]
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial_succ,
    Nat.cast_sub hn1, Nat.cast_sub hn2, Nat.cast_sub hn3]
  field_simp
  ring

theorem fourRow_failure_uniform_upper {n : ℕ} (hn : 4 ≤ n) :
    1 - separationProbability (uniformBoard 4 n) 4 ≤ 87 / (16 * (n : ℝ)) := by
  rw [fourRow_failure_uniform hn]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hsmall : 6 / (n : ℝ) ^ 3 ≤ 11 / (n : ℝ) ^ 2 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (n : ℝ)]
  calc
    _ ≤ (29 / 32 : ℝ) * (6 / n) := by linarith
    _ = _ := by ring

/-- The complete contender premise gives the small cell second moment. -/
theorem fourRow_contender_cellSquareSum {n : ℕ} (hn : 4 ≤ n)
    {P : Board 4 n} (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4) :
    cellSquareSum P ≤ 87 / (16 * (n : ℝ)) :=
  (fourRow_cellSquareSum_le_failure hP).trans
    ((sub_le_sub_left hcont 1).trans (fourRow_failure_uniform_upper hn))

/-- Four entries in a column give its Cauchy bound against the actual cell moment. -/
theorem fourRow_colSum_sq_le_cellSquareSum {n : ℕ} (P : Board 4 n) (j : Fin n) :
    colSum P j ^ 2 ≤ 4 * cellSquareSum P := by
  have hcol : colSum P j ^ 2 ≤ 4 * ∑ i, P i j ^ 2 := by
    simpa [colSum, mul_comm] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 4 => P i j) (fun _ => (1 : ℝ))
  have hpart : (∑ i, P i j ^ 2) ≤ cellSquareSum P := by
    unfold cellSquareSum
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    exact Finset.single_le_sum (fun c _ => Finset.sum_nonneg fun i _ => sq_nonneg (P i c))
      (Finset.mem_univ j)
  linarith

/-- Initial column cap for every actual contender at N >= 500, including zero columns. -/
theorem fourRow_contender_initial_colSum {n : ℕ} (hn : 500 ≤ n)
    {P : Board 4 n} (hP : IsProbability P)
    (hcont : separationProbability (uniformBoard 4 n) 4 ≤ separationProbability P 4)
    (j : Fin n) : colSum P j < 21 / 100 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (500 : ℝ) ≤ n := by exact_mod_cast hn
  have hcell := fourRow_contender_cellSquareSum (by omega) hP hcont
  have hcol := fourRow_colSum_sq_le_cellSquareSum P j
  have hsmall : 87 / (16 * (n : ℝ)) < (21 / 100 : ℝ) ^ 2 / 4 := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  nlinarith [colSum_nonneg hP.1 j]

end DittertRybin
