import DR.Rectangular.FourRowAveraging

/-! Signed identities, empty/boundary boards, and the actual four-sample factor. -/

open DittertRybin DittertRybin.Certificates
open scoped BigOperators

example {n : ℕ} (T : Board 4 n) :
    fourRowBlendKernel T = averagingKernel T 2 :=
  fourRowBlendKernel_eq_averagingKernel T

example : elementarySymmetric ![1,-2,3] 2 = -5 := by
  have h := fourRow_elementarySymmetric_two ![1,-2,3]
  norm_num [Fin.sum_univ_succ] at h
  linarith

example (T : Board 4 0) : averagingKernel T 2 = 0 := by
  rw [← fourRowBlendKernel_eq_averagingKernel]
  have hz (i j : Fin 4) : fourRowColumnComplement (fun _ => 0) i j = 0 := by
    simpa using fourRowColumnComplement_scale (fun _ => 1) 0 i j
  have hr : rowSum T = fun _ => 0 := by funext i; simp [rowSum]
  ext i j
  simp [fourRowBlendKernel, fourRowColumnSquareMass, fourRowComplementCorrection,
    totalMass, hr, hz]

private def diagonalBoard : Board 4 4 := fun i j => if i = j then 1 else 0

private theorem diagonal_remaining_quadratic :
    quadraticValue (fourRowBlendKernel (eraseColumns diagonalBoard {0,1}))
      (fun i => diagonalBoard i 0 - diagonalBoard i 1) = 2 := by
  let T := eraseColumns diagonalBoard {0,1}
  have hm : totalMass T = 2 := by
    norm_num [totalMass, rowSum, Fin.sum_univ_four, T, eraseColumns, diagonalBoard]
    norm_num [Fin.ext_iff]
  have hα : fourRowColumnSquareMass T = 2 := by
    norm_num [fourRowColumnSquareMass, colSum, Fin.sum_univ_four, T, eraseColumns, diagonalBoard]
    norm_num [Fin.ext_iff]
  have hd (i : Fin 4) : fourRowBlendKernel T i i = 1 := by
    norm_num [fourRowBlendKernel, hm, hα, fourRowColumnComplement, fourRowComplementCorrection]
  have h01 : ((Finset.univ.erase (0 : Fin 4)).erase 1) = {2,3} := by decide
  have hprod (v : Fin 4 → ℝ) : fourRowColumnComplement v 0 1 = v 2 * v 3 := by
    rw [fourRowColumnComplement, if_neg (by decide), h01, Finset.prod_pair (by decide)]
  have hcross : fourRowBlendKernel T 0 1 = 0 := by
    simp only [fourRowBlendKernel, hm, hα, hprod, fourRowComplementCorrection]
    simp only [rowSum, Fin.sum_univ_four]
    norm_num [T, eraseColumns, diagonalBoard]
    norm_num [Fin.ext_iff]
  have hcross' : fourRowBlendKernel T 1 0 = 0 := by
    rw [fourRowBlendKernel_eq_averagingKernel, averagingKernel_symmetric,
      ← fourRowBlendKernel_eq_averagingKernel, hcross]
  change quadraticValue (fourRowBlendKernel T) _ = 2
  simp only [quadraticValue, Fin.sum_univ_four]
  norm_num [diagonalBoard]
  norm_num [Fin.ext_iff]
  rw [hd, hd, hcross, hcross']
  norm_num

/-- A sparse board gives a nonzero exact gain and fixes the factorial normalization. -/
private theorem diagonal_gain :
    separationProbability (blendColumns diagonalBoard 0 1 (1/2)) 4 -
      separationProbability diagonalBoard 4 = 12 := by
  rw [fourRow_separationProbability_blend_identity _ _ _ (by decide),
    diagonal_remaining_quadratic]
  norm_num

example : ¬ (separationProbability (blendColumns diagonalBoard 0 1 (1/2)) 4 -
    separationProbability diagonalBoard 4 =
      12 * ((1/2) * (1 - 1/2)) * quadraticValue
        (fourRowBlendKernel (eraseColumns diagonalBoard {0,1}))
        (fun i => diagonalBoard i 0 - diagonalBoard i 1)) := by
  rw [diagonal_gain, diagonal_remaining_quadratic]
  norm_num

/-- The final rigidity statement is on the full probability simplex, with concentration explicit. -/
example {n : ℕ} (P : Board 4 n) (hP : IsProbability P)
    (hmax : ∀ Q : Board 4 n, IsProbability Q → separationProbability Q 4 ≤
      separationProbability P 4) (a b : Fin n)
    (hm : 493 / 500 ≤ totalMass (eraseColumns P {a,b}))
    (hα : fourRowColumnSquareMass (eraseColumns P {a,b}) ≤ 7 / 2500)
    (hν : fourRowMarginalVariance (fun i => rowSum (eraseColumns P {a,b}) i /
      totalMass (eraseColumns P {a,b})) ≤ 1 / 40) :
    ∀ i, P i a = P i b :=
  fourRow_columns_eq_of_globalMax P hP hmax a b hm hα hν

#print axioms DittertRybin.fourRow_rookSum_two
#print axioms DittertRybin.fourRowBlendKernel_eq_averagingKernel
#print axioms DittertRybin.fourRow_separationProbability_blend_identity
#print axioms DittertRybin.fourRow_separationProbability_blend_gain
#print axioms DittertRybin.fourRow_columns_eq_of_globalMax
