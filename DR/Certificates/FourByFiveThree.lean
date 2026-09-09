import DR.Certificates.FourByFiveThreeCheck
import DR.Certificates.FourByFiveThreeOrbits

/-! The four exact shifted Gram certificates imply real spectral floors for
the actual formula-defined 4x5 seeds and all physical multiplier pairs. -/
namespace DittertRybin.Certificates
open scoped BigOperators

theorem fourByFiveThreeShift_posSemidef (s : Fin 4) :
    ((fourByFiveThreeShift s).map (fun q : ℚ => (q:ℝ))).PosSemidef := by
  apply rational_principal_gram_posSemidef (fourByFiveThreeShift s)
    (fourByFiveThreeMatrix_checks s).1 (fun _ => 1)
  · intro i
    simpa only [mul_one] using (fourByFiveThreeMatrix_checks s).2.1 i
  · norm_num
  · exact fourByFiveThreeGram_valid s

theorem fourByFiveThreeSeed_lower (s : Fin 4) (x : Fin 20 → ℝ) :
    (2/5:ℝ)*((∑ i,x i^2)-(∑ i,x i)^2/20)≤
      quadraticValue ((fourByFiveThreeSeed s).map (fun q : ℚ => (q:ℝ))) x := by
  have h := quadraticValue_lower_of_centered_shift (fourByFiveThreeSeed s) (2/5)
    (fourByFiveThreeShift_posSemidef s) x
  norm_num only [Rat.cast_div,Rat.cast_ofNat,Nat.cast_ofNat] at h
  exact h

theorem fourByFiveThreeMatrix_lower (e f : Fin 20) (x : Fin 20 → ℝ) :
    (2/5:ℝ)*((∑ i,x i^2)-(∑ i,x i)^2/20)≤
      quadraticValue ((fourByFiveThreeMatrix e f).map (fun q : ℚ => (q:ℝ))) x := by
  let σ := fourByFiveThreePairPermutation e f
  have h := fourByFiveThreeSeed_lower (fourByFiveThreePairType e f) (fun i => x (σ.symm i))
  have hs : (∑ i,x (σ.symm i)^2)=∑ i,x i^2 := Equiv.sum_comp σ.symm (fun i => x i^2)
  rw [hs,Equiv.sum_comp σ.symm x] at h
  rw [fourByFiveThreeMatrix_conjugate]
  have hq := quadraticValue_submatrix_equiv
    ((fourByFiveThreeSeed (fourByFiveThreePairType e f)).map (fun q : ℚ => (q:ℝ))) σ x
  exact hq.symm ▸ h

end DittertRybin.Certificates
