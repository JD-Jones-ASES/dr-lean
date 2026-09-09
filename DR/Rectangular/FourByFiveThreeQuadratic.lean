import DR.Rectangular.FourByFiveThreeGeometry
import DR.Certificates.FourByFiveThree
import DR.Certificates.WeightedPair

/-! The finite certificate matrix uses twenty flattened cells. This bridge
identifies its quadratic form with the literal row/column-label matrix used
by the signed iid quartic identity. No sign or normalization is assumed. -/
namespace DittertRybin
open scoped BigOperators
open Certificates

theorem fourByFiveThree_cell_quadratic (P : Board 4 5) (e f : Fin 4 × Fin 5) :
    quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
      (fun a => P a.1 a.2) =
      quadraticValue ((fourByFiveThreeMatrix (fourByFiveThreeCell e)
        (fourByFiveThreeCell f)).map (fun q : ℚ => (q:ℝ))) (fourByFiveThreeFlat P) := by
  have hmatrix : finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f =
      (((fourByFiveThreeMatrix (fourByFiveThreeCell e) (fourByFiveThreeCell f)).map
        (fun q : ℚ => (q:ℝ))).submatrix fourByFiveThreeCell fourByFiveThreeCell) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.map_apply, fourByFiveThreeMatrix,
      Equiv.symm_apply_apply, finiteK3Entry]
  rw [hmatrix]
  exact quadraticValue_submatrix_equiv _ fourByFiveThreeCell _

/-- The actual cell-label kernel has the certified floor on every mass-one board,
including signed boards and the constant direction. -/
theorem fourByFiveThree_cell_quadratic_lower (P : Board 4 5)
    (hmass : totalMass P=1) (e f : Fin 4 × Fin 5) :
    (2/5:ℝ)*fourByFiveThreeEnergy P≤
      quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
        (fun a => P a.1 a.2) := by
  rw [fourByFiveThree_cell_quadratic]
  have h := fourByFiveThreeMatrix_lower (fourByFiveThreeCell e) (fourByFiveThreeCell f)
    (fourByFiveThreeFlat P)
  rw [fourByFiveThree_centered_sum _ ((fourByFiveThree_sum_flat P).trans hmass),
    fourByFiveThree_energy_flat] at h
  exact h

/-- Positivity of the multiplier weights gives the full-simplex quadratic gap.
Its identification with the actual probability gap is a separate quartic identity. -/
theorem fourByFiveThree_weighted_quadratic_lower {P : Board 4 5} (hP : IsProbability P) :
    (1/5:ℝ)*fourByFiveThreeEnergy P≤
      ∑ e : Fin 4 × Fin 5,∑ f : Fin 4 × Fin 5,
        unorderedPairWeight e f*P e.1 e.2*P f.1 f.2*
          quadraticValue (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)) e f)
            (fun a => P a.1 a.2) := by
  have h := weightedPair_quadratic_lower (fun a : Fin 4 × Fin 5 => P a.1 a.2)
    (fun a => hP.1 a.1 a.2) ((sum_cell_weights P).trans hP.2)
    (finiteK3Entry (fun k => (fourByFiveThreeCoefficient k:ℝ)))
    (fun a => P a.1 a.2) (2/5) (fourByFiveThreeEnergy P) (by norm_num)
    (fourByFiveThreeEnergy_nonneg P) (fourByFiveThree_cell_quadratic_lower P hP.2)
  norm_num only [div_div] at h
  convert h using 1

end DittertRybin
