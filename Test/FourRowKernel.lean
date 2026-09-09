import DR.Rectangular.FourRowBlendBounds

/-! Kernel domains, boundary columns, and controls for the exact constants. -/

open DittertRybin DittertRybin.Certificates
open scoped BigOperators

example (s x : Fin 4 → ℝ) (hs : ∀ i, 0 ≤ s i) (hm : ∑ i, s i = 1)
    (hv : (∑ i, (s i - 1 / 4) ^ 2) ≤ 1 / 40) :
    (97 / 5792 : ℝ) * (∑ i, x i ^ 2) ≤
      ∑ i, ∑ j, x i * fourRowLeadingKernel s i j * x j :=
  fourRowLeadingKernel_near_lower s x hs hm hv

example (x : Fin 4 → ℝ) :
    quadraticValue (fourRowLeadingKernel (fun _ => (1 / 4 : ℝ))) x =
      (1 / 8 : ℝ) * (∑ i, x i ^ 2) + (7 / 8 : ℝ) * (∑ i, x i) ^ 2 := by
  rw [fourRowLeadingKernel_quadratic _ x (by norm_num)]
  norm_num [fourRowReferenceQuadratic, div_eq_mul_inv, mul_pow,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

example : ¬ (∀ x : Fin 4 → ℝ,
    fourRowReferenceQuadratic (fun _ => (1 / 4 : ℝ)) x ≤
      quadraticValue (fourRowLeadingKernel (fun _ => (1 / 4 : ℝ))) x) := by
  intro h
  have h' := h (fun _ => 1)
  rw [fourRowLeadingKernel_quadratic _ _ (by norm_num)] at h'
  norm_num [fourRowReferenceQuadratic] at h'

example : fourRowLeadingKernel ![0,1/3,1/3,1/3] 1 2 = 1 := by
  have he : ((Finset.univ.erase (1 : Fin 4)).erase 2) = {0,3} := by decide
  norm_num [fourRowLeadingKernel, he, Fin.ext_iff, Finset.prod_insert]

private noncomputable def boundaryColumn : Board 4 1 := fun i _ => if i.val = 0 then 0 else 1

private theorem boundaryColumn_0 : boundaryColumn 0 0 = 0 := rfl
private theorem boundaryColumn_1 : boundaryColumn 1 0 = 1 := rfl
private theorem boundaryColumn_2 : boundaryColumn 2 0 = 1 := rfl
private theorem boundaryColumn_3 : boundaryColumn 3 0 = 1 := rfl

private theorem boundaryColumn_row :
    (∑ j, fourRowComplementCorrection boundaryColumn 0 j) = 3 := by
  have h01 : ((Finset.univ.erase (0 : Fin 4)).erase 1) = {2,3} := by decide
  have h02 : ((Finset.univ.erase (0 : Fin 4)).erase 2) = {1,3} := by decide
  have h03 : ((Finset.univ.erase (0 : Fin 4)).erase 3) = {1,2} := by decide
  have hd : fourRowComplementCorrection boundaryColumn 0 0 = 0 := by
    simp [fourRowComplementCorrection, fourRowColumnComplement]
  have h1 : fourRowComplementCorrection boundaryColumn 0 1 = 1 := by
    simp only [fourRowComplementCorrection, Fin.sum_univ_one]
    rw [fourRowColumnComplement, if_neg (by decide), h01]
    rw [Finset.prod_pair (by decide), boundaryColumn_2, boundaryColumn_3]
    norm_num
  have h2 : fourRowComplementCorrection boundaryColumn 0 2 = 1 := by
    simp only [fourRowComplementCorrection, Fin.sum_univ_one]
    rw [fourRowColumnComplement, if_neg (by decide), h02]
    rw [Finset.prod_pair (by decide), boundaryColumn_1, boundaryColumn_3]
    norm_num
  have h3 : fourRowComplementCorrection boundaryColumn 0 3 = 1 := by
    simp only [fourRowComplementCorrection, Fin.sum_univ_one]
    rw [fourRowColumnComplement, if_neg (by decide), h03]
    rw [Finset.prod_pair (by decide), boundaryColumn_1, boundaryColumn_2]
    norm_num
  rw [Fin.sum_univ_four, hd, h1, h2, h3]
  norm_num

private theorem boundaryColumn_squareMass : fourRowColumnSquareMass boundaryColumn = 9 := by
  rw [fourRowColumnSquareMass, Fin.sum_univ_one, colSum, Fin.sum_univ_four,
    boundaryColumn_0, boundaryColumn_1, boundaryColumn_2, boundaryColumn_3]
  norm_num

example : fourRowColumnSquareMass boundaryColumn = 9 := boundaryColumn_squareMass

example : ¬ ((∑ j, fourRowComplementCorrection boundaryColumn 0 j) ≤
    fourRowColumnSquareMass boundaryColumn / 4) := by
  rw [boundaryColumn_row, boundaryColumn_squareMass]
  norm_num

/-- Column masses may vanish; only their genuine mass and second moment are constrained. -/
example {n : ℕ} (c : Fin n → ℝ) (hc : ∀ j, 0 ≤ c j) (hm : ∑ j, c j = 1)
    (hα : (∑ j, c j ^ 2) ≤ 7 / 2500) (x : Fin 4 → ℝ) :
    (13965659 / 8688000000 : ℝ) * (∑ i, x i ^ 2) ≤
      quadraticValue (fourRowBlendKernel (fun _ j => c j / 4)) x := by
  let T : Board 4 n := fun _ j => c j / 4
  have hT : ∀ i j, 0 ≤ T i j := fun _ j => div_nonneg (hc j) (by norm_num)
  have hrow (i : Fin 4) : rowSum T i = 1 / 4 := by
    simp [rowSum, T, ← Finset.sum_div, hm]
  have hmass : totalMass T = 1 := by simp [totalMass, hrow]
  have hcol (j : Fin n) : colSum T j = c j := by norm_num [colSum, T]; ring
  apply fourRowBlendKernel_uniform_floor T hT
  · norm_num [hmass]
  · simpa [fourRowColumnSquareMass, hcol] using hα
  · norm_num [fourRowMarginalVariance, hrow, hmass]

#print axioms DittertRybin.fourRow_rank_one_cauchy
#print axioms DittertRybin.fourRowLeadingKernel_near_lower
#print axioms DittertRybin.fourRowComplementCorrection_quadratic_lower
#print axioms DittertRybin.fourRowBlendKernel_uniform_floor
