import DR.Certificates.SpectralFourEntries
import DR.Certificates.SpectralFourGramCheck
import DR.Certificates.SpectralFourKernelCheck

/-! Exact PSD and kernel consequences for the formula-defined order-four seeds.
The sextic polynomial identity and full multiplier-orbit coverage are separate obligations. -/

namespace DittertRybin.Certificates
open scoped BigOperators

/-- The checked entry roles recover the actual formula-defined physical seed matrices. -/
theorem spectralFourSeedMatrix_eq_table (s : Fin 33) :
    spectralFourSeedMatrix s = spectralFourTableMatrix s := by
  ext i j
  change spectralFourRoleCoefficient (spectralFourCanonicalRoleKey (spectralFourMultipliers.get s) i j) = _
  rw [← spectralFourEntryRoleKey s i j, spectralFourRoleCoefficient_catalog]
  rfl

/-- All fifteen pivots are positive for each of the thirty-three shifted principal blocks. -/
theorem spectralFourShift_principal_posDef (s : Fin 33) :
    (((spectralFourShift s).submatrix Fin.castSucc Fin.castSucc).map (fun q : ℚ => (q : ℝ))).PosDef := by
  let L : Matrix (Fin 15) (Fin 15) ℚ := Matrix.of (fun i j => (spectralFourCertificate s).factor j i)
  apply GramCertificate.ofLDL_posDef L (spectralFourCertificate s).weights
    ((spectralFourShift s).submatrix Fin.castSucc Fin.castSucc)
    (spectralFourFactor_checks s).1
  · intro i j
    rw [(spectralFourCertificate_valid s).2 i j]
    unfold weightedGram
    apply Finset.sum_congr rfl
    intro a _
    dsimp [L]
    ring
  · exact (spectralFourFactor_checks s).2.1
  · intro i
    exact ne_of_gt ((spectralFourFactor_checks s).2.2 i)

/-- The checked constant kernel lifts all thirty-three principal certificates to full PSD. -/
theorem spectralFourShift_posSemidef (s : Fin 33) :
    ((spectralFourSeedMatrix s - (1 / 10 : ℚ) • centeringMatrix 16).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  rw [spectralFourSeedMatrix_eq_table]
  apply rational_principal_gram_posSemidef (spectralFourShift s)
    (spectralFourMatrix_checks s).2.2.1 (fun _ => 1)
  · intro i
    simpa only [mul_one] using (spectralFourMatrix_checks s).2.2.2 i
  · norm_num
  · exact spectralFourCertificate_valid s

/-- The quantitative real spectral bound for every actual physical seed. -/
theorem spectralFourSeedMatrix_lower (s : Fin 33) (x : Fin 16 → ℝ) :
    (1 / 10 : ℝ) * ((∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / 16) ≤
      quadraticValue ((spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ))) x := by
  have h := quadraticValue_lower_of_centered_shift (spectralFourSeedMatrix s) (1 / 10)
    (spectralFourShift_posSemidef s) x
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat] at h
  exact h


theorem sum_centered_sixteen (x : Fin 16 → ℝ) :
    (∑ i, (x i - (∑ j, x j) / 16) ^ 2) = (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / 16 := by
  let μ := (∑ j, x j) / 16
  have hp (i : Fin 16) : (x i - μ) ^ 2 = x i ^ 2 - 2 * μ * x i + μ ^ 2 := by ring
  change (∑ i, (x i - μ) ^ 2) = _
  simp_rw [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  dsimp [μ]
  ring

theorem rational_quadratic_constant_eq_zero (Q : Matrix (Fin 16) (Fin 16) ℚ)
    (hkernel : ∀ i, (∑ j, Q i j) = 0) (c : ℝ) :
    quadraticValue (Q.map (fun q : ℚ => (q : ℝ))) (fun _ => c) = 0 := by
  unfold quadraticValue
  apply Finset.sum_eq_zero
  intro i _
  simp only [Matrix.map_apply, ← Finset.sum_mul, ← Finset.mul_sum]
  have h : (∑ j, (Q i j : ℝ)) = 0 := by exact_mod_cast hkernel i
  rw [h]
  ring

theorem quadratic_kernel_of_tenth_centered_shift (Q : Matrix (Fin 16) (Fin 16) ℚ)
    (hkernel : ∀ i, (∑ j, Q i j) = 0)
    (hshift : ((Q - (1 / 10 : ℚ) • centeringMatrix 16).map (fun q : ℚ => (q : ℝ))).PosSemidef)
    (x : Fin 16 → ℝ) :
    quadraticValue (Q.map (fun q : ℚ => (q : ℝ))) x = 0 ↔ ∃ c : ℝ, ∀ i, x i = c := by
  constructor
  · intro hx
    have h := quadraticValue_lower_of_centered_shift Q (1 / 10) hshift x
    rw [hx] at h
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Nat.cast_ofNat] at h
    rw [← sum_centered_sixteen] at h
    have hn : 0 ≤ ∑ i, (x i - (∑ j, x j) / 16) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hz : (∑ i, (x i - (∑ j, x j) / 16) ^ 2) = 0 := by linarith
    refine ⟨(∑ j, x j) / 16, fun i => ?_⟩
    have hi := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i - (∑ j, x j) / 16))).mp hz i (Finset.mem_univ i)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · rintro ⟨c, hc⟩
    have heq : x = fun _ => c := funext hc
    rw [heq]
    exact rational_quadratic_constant_eq_zero Q hkernel c


/-- The quantitative bound in particular makes every full seed matrix PSD. -/
theorem spectralFourSeedMatrix_posSemidef (s : Fin 33) :
    ((spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.isHermitian_iff_isSymm]
    ext i j
    change (spectralFourSeedMatrix s j i : ℝ) = (spectralFourSeedMatrix s i j : ℝ)
    rw [spectralFourSeedMatrix_eq_table]
    exact congrArg (fun q : ℚ => (q : ℝ)) ((spectralFourMatrix_checks s).1 j i)
  · intro x
    have hcenter : 0 ≤ (∑ i, x i ^ 2) - (∑ i, x i) ^ 2 / 16 := by
      rw [← sum_centered_sixteen]
      exact Finset.sum_nonneg fun i _ => sq_nonneg _
    have h := (mul_nonneg (by norm_num : 0 ≤ (1 / 10 : ℝ)) hcenter).trans
      (spectralFourSeedMatrix_lower s x)
    simpa [quadraticValue_eq_dotProduct] using h

/-- Every seed kernel is exactly the constant vectors, including all boundary vectors. -/
theorem spectralFourSeedMatrix_kernel (s : Fin 33) (x : Fin 16 → ℝ) :
    quadraticValue ((spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ))) x = 0 ↔
      ∃ c : ℝ, ∀ i, x i = c := by
  apply quadratic_kernel_of_tenth_centered_shift (spectralFourSeedMatrix s)
  · rw [spectralFourSeedMatrix_eq_table]
    exact (spectralFourMatrix_checks s).2.1
  · exact spectralFourShift_posSemidef s

/-- The matrix nullspace itself is exactly the constant line. -/
theorem spectralFourSeedMatrix_mulVec_kernel (s : Fin 33) (x : Fin 16 → ℝ) :
    ((spectralFourSeedMatrix s).map (fun q : ℚ => (q : ℝ))).mulVec x = 0 ↔
      ∃ c : ℝ, ∀ i, x i = c := by
  constructor
  · intro hx
    apply (spectralFourSeedMatrix_kernel s x).mp
    rw [quadraticValue_eq_dotProduct, hx, dotProduct_zero]
  · rintro ⟨c, hc⟩
    ext i
    change (∑ j, (spectralFourSeedMatrix s i j : ℝ) * x j) = 0
    simp_rw [hc, ← Finset.sum_mul]
    have hrow : (∑ j, (spectralFourSeedMatrix s i j : ℝ)) = 0 := by
      rw [spectralFourSeedMatrix_eq_table]
      exact_mod_cast (spectralFourMatrix_checks s).2.1 i
    rw [hrow, zero_mul]

end DittertRybin.Certificates
