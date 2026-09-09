import DR.Certificates.FourByFourThreeCheck

/-! Soundness of the exact rational 4x4 cubic seed on all real vectors. -/
namespace DittertRybin.Certificates
open scoped BigOperators

theorem fourByFourThreeShift_posSemidef :
    (fourByFourThreeShift.map (fun q : ℚ => (q:ℝ))).PosSemidef := by
  apply rational_principal_gram_posSemidef fourByFourThreeShift
    fourByFourThreeMatrix_checks.1 (fun _ => 1)
  · intro i
    simpa only [mul_one] using fourByFourThreeMatrix_checks.2.1 i
  · norm_num
  · exact fourByFourThreeGram_valid

theorem fourByFourThreeSeed_lower (x : Fin 16 → ℝ) :
    (1/20:ℝ)*((∑ i,x i^2)-(∑ i,x i)^2/16)≤
      quadraticValue (fourByFourThreeSeed.map (fun q : ℚ => (q:ℝ))) x := by
  have h := quadraticValue_lower_of_centered_shift fourByFourThreeSeed (1/20)
    fourByFourThreeShift_posSemidef x
  norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Nat.cast_ofNat] at h
  exact h

/-- Every multiplier matrix is an actual permutation conjugate, so it has the same floor. -/
theorem fourByFourThreeMatrix_lower (e : Fin 16) (x : Fin 16 → ℝ) :
    (1/20:ℝ)*((∑ i,x i^2)-(∑ i,x i)^2/16)≤
      quadraticValue ((fourByFourThreeMatrix e).map (fun q : ℚ => (q:ℝ))) x := by
  let σ := fourByFourThreeSwap e
  have h := fourByFourThreeSeed_lower (fun i => x (σ.symm i))
  have hq : quadraticValue (fourByFourThreeSeed.map (fun q : ℚ => (q:ℝ)))
      (fun i => x (σ.symm i))=
        quadraticValue ((fourByFourThreeMatrix e).map (fun q : ℚ => (q:ℝ))) x := by
    unfold quadraticValue
    rw [← Equiv.sum_comp σ]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Equiv.sum_comp σ]
    simp only [Equiv.symm_apply_apply,Matrix.map_apply,fourByFourThreeMatrix,Matrix.submatrix_apply,σ]
  rw [hq] at h
  have hs : (∑ i,x (σ.symm i)^2)=∑ i,x i^2 := Equiv.sum_comp σ.symm (fun i => x i^2)
  rw [hs,Equiv.sum_comp σ.symm x] at h
  exact h

end DittertRybin.Certificates
