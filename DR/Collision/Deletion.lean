import DR.Collision.Concentration
import DR.Collision.Thresholds
import DR.Collision.OccupationBounds

/-!
# Variance after deleting columns

Column deletion is represented by setting the deleted columns to zero.
The row sums are then centered at their new mean. Centering can only
decrease the squared norm, so the resulting row variance is controlled
by the original cell variance even when the deleted columns are unequal.
-/

open scoped BigOperators

namespace DittertRybin

/-- Keep a specified finite set of columns and set the others to zero. -/
def keepColumns {m n : ℕ} (P : Board m n) (S : Finset (Fin n)) : Board m n :=
  fun i j => if j ∈ S then P i j else 0

theorem rowSum_keepColumns {m n : ℕ} (P : Board m n) (S : Finset (Fin n)) (i : Fin m) :
    rowSum (keepColumns P S) i = ∑ j ∈ S, P i j := by
  simp [rowSum, keepColumns]

theorem colSum_keepColumns {m n : ℕ} (P : Board m n) (S : Finset (Fin n)) (j : Fin n) :
    colSum (keepColumns P S) j = if j ∈ S then colSum P j else 0 := by
  by_cases hj : j ∈ S <;> simp [colSum, keepColumns, hj]

theorem keepColumns_nonneg {m n : ℕ} {P : Board m n} (hP : ∀ i j, 0 ≤ P i j)
    (S : Finset (Fin n)) : ∀ i j, 0 ≤ keepColumns P S i j := by
  intro i j
  by_cases hj : j ∈ S <;> simp [keepColumns, hj, hP]

theorem totalMass_keepColumns {m n : ℕ} (P : Board m n) (S : Finset (Fin n)) :
    totalMass (keepColumns P S) = ∑ j ∈ S, colSum P j := by
  rw [totalMass_eq_sum_colSum]
  simp [colSum_keepColumns]

theorem rowSum_keepColumns_le {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (S : Finset (Fin n)) (i : Fin m) :
    rowSum (keepColumns P S) i ≤ rowSum P i := by
  rw [rowSum_keepColumns]
  exact Finset.sum_le_univ_sum_of_nonneg (fun j => hP i j)

theorem colSum_keepColumns_le {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (S : Finset (Fin n)) (j : Fin n) :
    colSum (keepColumns P S) j ≤ colSum P j := by
  rw [colSum_keepColumns]
  split_ifs
  · exact le_rfl
  · exact colSum_nonneg hP j

/-- Deleting two distinct columns subtracts exactly their two marginal masses. -/
theorem totalMass_delete_two {m n : ℕ} (P : Board m n) (a b : Fin n) (hab : a ≠ b) :
    totalMass (keepColumns P ({a, b}ᶜ)) = totalMass P - colSum P a - colSum P b := by
  rw [totalMass_keepColumns]
  have h := Finset.sum_add_sum_compl ({a, b} : Finset (Fin n)) (colSum P)
  rw [Finset.sum_pair hab, ← totalMass_eq_sum_colSum] at h
  linarith

/-- Divide all entries by the total mass; its probability interpretation needs positive mass. -/
noncomputable def normalizeBoard {m n : ℕ} (P : Board m n) : Board m n :=
  fun i j => P i j / totalMass P

theorem rowSum_normalizeBoard {m n : ℕ} (P : Board m n) (i : Fin m) :
    rowSum (normalizeBoard P) i = rowSum P i / totalMass P := by
  simp only [rowSum, normalizeBoard, Finset.sum_div]

theorem colSum_normalizeBoard {m n : ℕ} (P : Board m n) (j : Fin n) :
    colSum (normalizeBoard P) j = colSum P j / totalMass P := by
  simp only [colSum, normalizeBoard, Finset.sum_div]

theorem normalizeBoard_isProbability {m n : ℕ} {P : Board m n}
    (hP : ∀ i j, 0 ≤ P i j) (hμ : 0 < totalMass P) : IsProbability (normalizeBoard P) := by
  constructor
  · intro i j
    exact div_nonneg (hP i j) hμ.le
  · simp only [totalMass, rowSum_normalizeBoard, ← Finset.sum_div]
    exact div_self (ne_of_gt hμ)

/-- Normalizing the retained columns increases marginal bounds by at most inverse retained mass. -/
theorem peakMarginal_normalize_keepColumns_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (S : Finset (Fin n))
    (hμ : 0 < totalMass (keepColumns P S)) :
    peakMarginal (normalizeBoard (keepColumns P S)) ≤
      peakMarginal P / totalMass (keepColumns P S) := by
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  apply max_le
  · apply ciSup_le
    intro i
    rw [rowSum_normalizeBoard]
    exact div_le_div_of_nonneg_right
      ((rowSum_keepColumns_le hP.1 S i).trans (rowSum_le_peakMarginal P i)) hμ.le
  · apply ciSup_le
    intro j
    rw [colSum_normalizeBoard]
    exact div_le_div_of_nonneg_right
      ((colSum_keepColumns_le hP.1 S j).trans (colSum_le_peakMarginal P j)) hμ.le

/-- A peak marginal of at most one quarter leaves at least half the mass after any two deletions. -/
theorem delete_two_mass_ge_half {m n : ℕ} {P : Board m n} (hP : IsProbability P)
    (hη : peakMarginal P ≤ 1 / 4) (a b : Fin n) (hab : a ≠ b) :
    (1 / 2 : ℝ) ≤ totalMass (keepColumns P ({a, b}ᶜ)) := by
  rw [totalMass_delete_two P a b hab, hP.2]
  linarith [colSum_le_peakMarginal P a, colSum_le_peakMarginal P b]

/-- Centering a finite real vector at its own mean minimizes squared distance to constants. -/
theorem sum_sq_center_le {m : ℕ} (hm : 0 < m) (v : Fin m → ℝ) (c : ℝ) :
    (∑ i, (v i - (∑ j, v j) / m) ^ 2) ≤ ∑ i, (v i - c) ^ 2 := by
  let μ : ℝ := (∑ j, v j) / m
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hcenter : (∑ i, (v i - μ)) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, μ]
    field_simp
    ring
  have he (i : Fin m) : (v i - c) ^ 2 =
      (v i - μ) ^ 2 + 2 * (μ - c) * (v i - μ) + (μ - c) ^ 2 := by ring
  have hid : (∑ i, (v i - c) ^ 2) =
      (∑ i, (v i - μ) ^ 2) + (m : ℝ) * (μ - c) ^ 2 := by
    simp only [he, Finset.sum_add_distrib, ← Finset.mul_sum, hcenter,
      mul_zero, add_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hid]
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _))

/-- The centered row-sum energy after any column deletion is at most N times cell variance. -/
theorem keepColumns_centered_row_sq_le {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (S : Finset (Fin n)) :
    (∑ i, (rowSum (keepColumns P S) i - totalMass (keepColumns P S) / m) ^ 2) ≤
      (n : ℝ) * cellVariance P := by
  let c : ℝ := S.card * ((m : ℝ) * n)⁻¹
  have hcenter := sum_sq_center_le hm (rowSum (keepColumns P S)) c
  have hrow (i : Fin m) :
      (rowSum (keepColumns P S) i - c) ^ 2 ≤
        (n : ℝ) * ∑ j, (P i j - uniformBoard m n i j) ^ 2 := by
    have heq : rowSum (keepColumns P S) i - c =
        ∑ j ∈ S, (P i j - uniformBoard m n i j) := by
      simp [rowSum_keepColumns, Finset.sum_sub_distrib, uniformBoard, c]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S
      (fun j => P i j - uniformBoard m n i j) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    have hS : (S.card : ℝ) ≤ n := by
      exact_mod_cast (show S.card ≤ n by simpa using Finset.card_le_univ S)
    have hsum : (∑ j ∈ S, (P i j - uniformBoard m n i j) ^ 2) ≤
        ∑ j, (P i j - uniformBoard m n i j) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg _)
    rw [heq]
    apply hcs.trans
    calc
      _ ≤ (∑ j, (P i j - uniformBoard m n i j) ^ 2) * (n : ℝ) :=
        mul_le_mul hsum hS (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = _ := mul_comm _ _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hrow i)
  rw [← Finset.mul_sum] at hsum
  have hv : (∑ i, ∑ j, (P i j - uniformBoard m n i j) ^ 2) = cellVariance P := by
    simp only [cellVariance, Fintype.sum_prod_type]
  rw [hv] at hsum
  exact hcenter.trans hsum

/-- Normalization costs exactly the inverse square of the retained mass. -/
theorem normalize_keepColumns_row_variance_le {m n : ℕ} (hm : 0 < m)
    (P : Board m n) (S : Finset (Fin n)) (hμ : 0 < totalMass (keepColumns P S)) :
    (m : ℝ) * (∑ i, (rowSum (normalizeBoard (keepColumns P S)) i - (m : ℝ)⁻¹) ^ 2) ≤
      normalizedVariance P / totalMass (keepColumns P S) ^ 2 := by
  let T := keepColumns P S
  let μ := totalMass T
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hμ0 : μ ≠ 0 := ne_of_gt hμ
  have hpoint (i : Fin m) :
      (rowSum (normalizeBoard T) i - (m : ℝ)⁻¹) ^ 2 * μ ^ 2 =
        (rowSum T i - μ / m) ^ 2 := by
    rw [rowSum_normalizeBoard]
    change (rowSum T i / μ - (m : ℝ)⁻¹) ^ 2 * μ ^ 2 = _
    field_simp
  apply (le_div_iff₀ (sq_pos_of_pos hμ)).mpr
  change ((m : ℝ) * ∑ i, (rowSum (normalizeBoard T) i - (m : ℝ)⁻¹) ^ 2) * μ ^ 2 ≤ _
  rw [mul_assoc, Finset.sum_mul]
  simp_rw [hpoint]
  simpa only [normalizedVariance, mul_assoc] using
    mul_le_mul_of_nonneg_left (keepColumns_centered_row_sq_le hm P S) (Nat.cast_nonneg m)

/-- Retaining half the mass gives the exact normalization losses used by the averaging argument. -/
theorem normalized_keepColumns_bounds {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (S : Finset (Fin n))
    (hmass : (1 / 2 : ℝ) ≤ totalMass (keepColumns P S)) :
    IsProbability (normalizeBoard (keepColumns P S)) ∧
      peakMarginal (normalizeBoard (keepColumns P S)) ≤ 2 * peakMarginal P ∧
      rowDispersion (normalizeBoard (keepColumns P S)) ≤ 4 * normalizedVariance P := by
  have hμ : 0 < totalMass (keepColumns P S) := by linarith
  have hη := peakMarginal_nonneg hm hP
  have hζ := normalizedVariance_nonneg P
  refine ⟨normalizeBoard_isProbability (keepColumns_nonneg hP.1 S) hμ, ?_, ?_⟩
  · apply (peakMarginal_normalize_keepColumns_le hm hn hP S hμ).trans
    apply (div_le_iff₀ hμ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmass hη]
  · have hvar : rowDispersion (normalizeBoard (keepColumns P S)) ≤
        normalizedVariance P / totalMass (keepColumns P S) ^ 2 := by
      simpa only [rowDispersion, one_div] using normalize_keepColumns_row_variance_le hm P S hμ
    apply hvar.trans
    calc
      _ ≤ normalizedVariance P / (1 / 2 : ℝ) ^ 2 := by gcongr
      _ = _ := by ring

/-- Every contender on a sufficiently large board meets the normalized two-column-deletion hypotheses. -/
theorem contender_deletion_bounds {m n k : ℕ} (hm : 0 < m) (hn : 0 < n)
    {P : Board m n} (hP : IsProbability P) (hk : 4 ≤ k)
    (hsize : largeBoardThreshold k ≤ min m n)
    (hcont : separationProbability (uniformBoard m n) k ≤ separationProbability P k)
    (a b : Fin n) (hab : a ≠ b) :
    (1 / 2 : ℝ) ≤ totalMass (keepColumns P ({a, b}ᶜ)) ∧
      IsProbability (normalizeBoard (keepColumns P ({a, b}ᶜ))) ∧
      peakMarginal (normalizeBoard (keepColumns P ({a, b}ᶜ))) ≤
        1 / (64 * ((k - 2 : ℕ) : ℝ) ^ 3) ∧
      rowDispersion (normalizeBoard (keepColumns P ({a, b}ᶜ))) ≤
        1 / (32 * ((k - 2 : ℕ) : ℝ)) := by
  let t : ℝ := (k - 2 : ℕ)
  have ht : 2 ≤ t := by dsimp [t]; exact_mod_cast (by omega : 2 ≤ k - 2)
  have ht3 : (2 : ℝ) ^ 3 ≤ t ^ 3 := by gcongr
  obtain ⟨hζ, hη⟩ := contender_smallness hm hn hP hk hsize hcont
  have hquarter : peakMarginal P ≤ 1 / 4 := by
    apply hη.le.trans
    apply (div_le_div_iff₀ (show 0 < 128 * t ^ 3 by positivity) (by norm_num)).mpr
    nlinarith [ht3]
  have hmass := delete_two_mass_ge_half hP hquarter a b hab
  obtain ⟨hprob, hpeak, hrow⟩ := normalized_keepColumns_bounds hm hn hP ({a, b}ᶜ) hmass
  refine ⟨hmass, hprob, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hη.le (show (0 : ℝ) ≤ 2 by norm_num)
    apply hpeak.trans
    calc
      2 * peakMarginal P ≤ 2 * (1 / (128 * t ^ 3)) := h
      _ = _ := by ring
  · have h := mul_le_mul_of_nonneg_left hζ.le (show (0 : ℝ) ≤ 4 by norm_num)
    apply hrow.trans
    calc
      4 * normalizedVariance P ≤ 4 * (1 / (128 * t)) := h
      _ = _ := by ring

end DittertRybin
