import DR.Rectangular.FourRowMinorantEqualRows

/-! Closed-face, normalization, and relabelling controls for the corrected minorant. -/

namespace DittertRybin.Test.FourRowMinorantFaces
open scoped BigOperators

-- Arbitrary designated pair, including every row-boundary pattern.
example (r v : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i) (hsr : ∑ i, r i = 1)
    (hv : ∀ i, 0 ≤ v i) (hsv : ∑ i, v i = 1)
    (hs : ∀ k, k ≠ 1 → k ≠ 3 → v k = 0) :
    0 ≤ fourRowMinorantHomogeneous r v :=
  fourRowMinorantHomogeneous_pair_nonneg r v hr hsr hv hsv 1 3 (by decide) hs

-- The full closed column simplex, with the zero row in an arbitrary position.
example (r v : Fin 4 → ℝ) (hr : ∀ i, 0 ≤ r i) (hsr : ∑ i, r i = 1)
    (hv : ∀ i, 0 ≤ v i) (hsv : ∑ i, v i = 1) (hz : r 2 = 0) :
    (∑ i, v i*(1-fourRowGaugeCollision r i)) ≤
      Certificates.quadraticValue (fourRowLeadingKernel r) v := by
  have h := fourRowMinorantHomogeneous_boundary_nonneg r v hr hsr hv hsv ⟨2,hz⟩
  rw [fourRowMinorantHomogeneous_eq_gap r v hsr hsv] at h
  linarith

-- Equality on the boundary: strict positivity cannot be substituted.
example : fourRowMinorantHomogeneous ![1/2,1/2,0,0] ![0,0,1/2,1/2] = 0 := by
  norm_num [fourRowMinorantHomogeneous,fourRowGaugeCollision,fourRow_complement_product,
    Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,Fin.ext_iff,
    -Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three]

-- The omitted-coordinate cube minorant from K=3 is false here; corrected g is essential.
example :
    Certificates.quadraticValue (fourRowLeadingKernel ![1/2,1/2,0,0]) ![0,0,1/2,1/2] = 3/4 ∧
    (3/4 : ℝ) < 7/9 := by
  norm_num [Certificates.quadraticValue,fourRowLeadingKernel,Fin.sum_univ_succ,
    Fin.prod_univ_succ,Finset.sum_erase,fourRow_complement_product,Fin.ext_iff,
    -Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three]

-- Cubic homogeneity remains an algebraic identity for negative row scaling.
example (r v : Fin 4 → ℝ) :
    fourRowMinorantHomogeneous (fun i => -2*r i) v =
      -8*fourRowMinorantHomogeneous r v := by
  rw [fourRowMinorantHomogeneous_smul]
  norm_num

-- Unequal active v coordinates, repeated positive rows, and nonunit row mass.
example : 0 ≤ fourRowMinorantHomogeneous ![1,2,2,3] ![1/4,1/2,1/4,0] :=
  fourRowMinorantHomogeneous_equal_rows_nonneg (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example :
    fourRowMinorantHomogeneous ![1,2,2,3] ![1/4,1/2,1/4,0] -
      fourRowMinorantHomogeneous ![1,2,2,3] ![1/4,3/8,3/8,0] = 3/2 := by
  have h := fourRowMinorantHomogeneous_equal_rows_average 1 2 3 (1/4) (1/2) (1/4)
  norm_num at h
  linarith

#print axioms fourRowPairCubic_minorant
#print axioms fourRowMinorantHomogeneous_permute
#print axioms fourRowMinorantHomogeneous_pair_nonneg
#print axioms fourRowMinorantHomogeneous_boundary_nonneg
#print axioms fourRowMinorantHomogeneous_smul
#print axioms fourRowMinorantHomogeneous_equal_rows_nonneg
#print axioms fourRowMinorantHomogeneous_equal_rows_probability

end DittertRybin.Test.FourRowMinorantFaces
