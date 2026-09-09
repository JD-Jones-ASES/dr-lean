import DR.Rectangular.FourRowGaugeConcentration
import DR.Rectangular.ThreeRowComparison

/-!
# Pair deletion and normalized row concentration

These estimates account for the actual two removed columns. They retain
zero cells and columns, and explicitly bound both the centering loss and
the division by retained mass.
-/

namespace DittertRybin

open scoped BigOperators

private theorem fourRow_deletion_norm_triangle (x y : Fin 4 → ℝ)
    (hx : (∑ i, x i ^ 2) ≤ (1 / 7 : ℝ) ^ 2)
    (hy : (∑ i, y i ^ 2) ≤ (49 / 4000 : ℝ) ^ 2) :
    (∑ i, (x i - y i) ^ 2) ≤ (1 / 7 + 49 / 4000 : ℝ) ^ 2 := by
  have hx0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy0 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hc' : (∑ i, x i * y i) ^ 2 ≤ ((1 / 7 : ℝ) * (49 / 4000)) ^ 2 := by
    nlinarith
  have hcross : -((1 / 7 : ℝ) * (49 / 4000)) ≤ ∑ i, x i * y i := by
    nlinarith [sq_nonneg ((∑ i, x i * y i) + (1 / 7) * (49 / 4000))]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc, ← Finset.mul_sum]
  linarith

theorem fourRowColumnSquareMass_erase_le {n : ℕ} (P : Board 4 n) (S : Finset (Fin n)) :
    fourRowColumnSquareMass (eraseColumns P S) ≤ fourRowColumnSquareMass P := by
  unfold fourRowColumnSquareMass
  apply Finset.sum_le_sum
  intro j _
  rw [colSum_eraseColumns]
  split_ifs
  · simpa using sq_nonneg (colSum P j)
  · exact le_rfl

/-- The actual deleted pair leaves the required mass and normalized row neighborhood. -/
theorem fourRow_pair_deletion_mass_variance {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hrow : fourRowMarginalVariance (rowSum P) * n < 10)
    (hcol : ∀ j, colSum P j < 7 / (2 * (n : ℝ)))
    (a b : Fin n) (hab : a ≠ b) :
    493 / 500 ≤ totalMass (eraseColumns P {a,b}) ∧
      fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
        totalMass (eraseColumns P {a,b})) < 1 / 40 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (500 : ℝ) ≤ n := by exact_mod_cast hn
  let τ : Fin 4 → ℝ := fun i => P i a + P i b
  let β := colSum P a + colSum P b
  let T := eraseColumns P {a,b}
  have hτ0 (i : Fin 4) : 0 ≤ τ i := add_nonneg (hP.1 i a) (hP.1 i b)
  have hβ0 : 0 ≤ β := add_nonneg (colSum_nonneg hP.1 a) (colSum_nonneg hP.1 b)
  have hτsum : ∑ i, τ i = β := by simp only [τ, β, Finset.sum_add_distrib, colSum]
  have hcap : 7 / (2 * (n : ℝ)) ≤ 7 / 1000 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hβ : β < 7 / 500 := by dsimp [β]; linarith [hcol a, hcol b]
  have hm : totalMass T = 1 - β := by
    dsimp [T, β]
    rw [totalMass_eraseColumns_pair P a b hab, hP.2]
    ring
  have hmlo : 493 / 500 ≤ totalMass T := by linarith
  have hmpos : 0 < totalMass T := by linarith
  have hvar0 := fourRowMarginalVariance_nonneg (rowSum P)
  have hx : (∑ i, (rowSum P i - 1 / 4) ^ 2) ≤ (1 / 7 : ℝ) ^ 2 := by
    change fourRowMarginalVariance (rowSum P) ≤ _
    nlinarith
  have hτsq : (∑ i, τ i ^ 2) ≤ β ^ 2 := by
    simpa only [hτsum] using Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun i _ => hτ0 i)
  have hcenter : (∑ i, (τ i - β / 4) ^ 2) = (∑ i, τ i ^ 2) - β ^ 2 / 4 := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, hτsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hy : (∑ i, (τ i - β / 4) ^ 2) ≤ (49 / 4000 : ℝ) ^ 2 := by
    rw [hcenter]
    nlinarith
  have hE := fourRow_deletion_norm_triangle (fun i => rowSum P i - 1/4)
    (fun i => τ i - β/4) hx hy
  have hpoint (i : Fin 4) : rowSum T i / totalMass T - 1/4 =
      ((rowSum P i - 1/4) - (τ i - β/4)) / totalMass T := by
    have hr : rowSum T i = rowSum P i - τ i := by
      dsimp [T, τ]
      rw [rowSum_eraseColumns_pair P a b hab]
      ring
    rw [hr]
    field_simp
    nlinarith [hm]
  have hvariance : fourRowMarginalVariance (fun i => rowSum T i / totalMass T) =
      (∑ i, ((rowSum P i - 1/4) - (τ i - β/4)) ^ 2) / totalMass T ^ 2 := by
    simp only [fourRowMarginalVariance, hpoint, div_pow, ← Finset.sum_div]
  refine ⟨hmlo, ?_⟩
  rw [hvariance]
  calc
    _ ≤ (1 / 7 + 49 / 4000 : ℝ) ^ 2 / totalMass T ^ 2 :=
      div_le_div_of_nonneg_right hE (sq_nonneg _)
    _ ≤ (1 / 7 + 49 / 4000 : ℝ) ^ 2 / (493 / 500) ^ 2 := by
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num)
      nlinarith
    _ < 1 / 40 := by norm_num

/-- The three kernel hypotheses follow from the raw, unnormalized concentration bounds. -/
theorem fourRow_pair_deletion_bounds {n : ℕ} (hn : 500 ≤ n)
    (P : Board 4 n) (hP : IsProbability P)
    (hrow : fourRowMarginalVariance (rowSum P) * n < 10)
    (hcol : ∀ j, colSum P j < 7 / (2 * (n : ℝ)))
    (hsecond : fourRowColumnSquareMass P < 7 / (5 * (n : ℝ)))
    (a b : Fin n) (hab : a ≠ b) :
    493 / 500 ≤ totalMass (eraseColumns P {a,b}) ∧
      fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500 ∧
      fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
        totalMass (eraseColumns P {a,b})) ≤ 1 / 40 := by
  obtain ⟨hm, hν⟩ := fourRow_pair_deletion_mass_variance hn P hP hrow hcol a b hab
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnreal : (500 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨hm, ?_, hν.le⟩
  apply (fourRowColumnSquareMass_erase_le P {a,b}).trans
  apply hsecond.le.trans
  apply (div_le_iff₀ (by positivity)).mpr
  linarith

end DittertRybin
