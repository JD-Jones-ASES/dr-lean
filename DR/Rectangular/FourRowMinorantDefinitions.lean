import DR.Rectangular.FourRowGauge
import Mathlib.Tactic.Ring

/-!
# The corrected four-row minorant objective

The homogeneous expression has degree three in the row coordinates. Its pair
sum is ordered and therefore carries coefficient two, equivalent to the
coefficient four on unordered pairs. Nothing here asserts positivity.
-/

namespace DittertRybin
open scoped BigOperators

noncomputable def fourRowMinorantHomogeneous (r v : Fin 4 → ℝ) : ℝ :=
  (∑ i, v i*fourRowGaugeCollision r i)-2*(∑ i, r i)*
    (∑ i, ∑ j ∈ Finset.univ.erase i,
      v i*v j*∏ k ∈ (Finset.univ.erase i).erase j, r k)

noncomputable def fourRowRepeatedMinorant (x z T : ℝ) : ℝ :=
  2*T*(1+z+z^2)+(1-T)*(x^2+x+z*(x^2+1)+z^2*(x+1))-
    (x+2+z)*z*(4*T*(1-T)+x*(1-T)^2)

theorem fourRow_complement_product (r : Fin 4 → ℝ) (i j : Fin 4) :
    (∏ k ∈ (Finset.univ.erase i).erase j, r k) =
      ∏ k, if k ≠ i ∧ k ≠ j then r k else 1 := by
  classical
  have he : (Finset.univ.erase i).erase j =
      Finset.univ.filter (fun k : Fin 4 => k ≠ i ∧ k ≠ j) := by
    ext k
    simp [and_comm]
  rw [he,Finset.prod_filter]

/-- The repeated-row polynomial is the actual homogeneous excess on its stated family. -/
theorem fourRowMinorantHomogeneous_repeated (x z T : ℝ) :
    fourRowMinorantHomogeneous ![x,1,1,z] ![T,(1-T)/2,(1-T)/2,0] =
      fourRowRepeatedMinorant x z T := by
  norm_num [fourRowMinorantHomogeneous,fourRowGaugeCollision,fourRowRepeatedMinorant,
    fourRow_complement_product,Fin.sum_univ_succ,Fin.prod_univ_succ,Finset.sum_erase,
    Fin.ext_iff,-Fin.val_eq_zero_iff,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

/-- On both probability simplices the homogeneous excess is exactly the desired minorant gap. -/
theorem fourRowMinorantHomogeneous_eq_gap (r v : Fin 4 → ℝ)
    (hr : ∑ i, r i = 1) (hv : ∑ i, v i = 1) :
    fourRowMinorantHomogeneous r v =
      Certificates.quadraticValue (fourRowLeadingKernel r) v-
        ∑ i, v i*(1-fourRowGaugeCollision r i) := by
  simp only [fourRowMinorantHomogeneous,hr]
  have hvsq : (∑ i, v i)^2 = 1 := by rw [hv]; norm_num
  norm_num [Fin.sum_univ_succ] at hvsq hv
  norm_num [Certificates.quadraticValue,fourRowLeadingKernel,Fin.sum_univ_succ,
    Finset.sum_erase,Fin.ext_iff,-Fin.val_eq_zero_iff]
  nlinarith [hvsq]

end DittertRybin
