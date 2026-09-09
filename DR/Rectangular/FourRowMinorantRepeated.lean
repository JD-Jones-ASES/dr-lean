import DR.Rectangular.FourRowMinorantDefinitions
import DR.Certificates.FourRowMinorantBernstein
import DR.Certificates.FourRowMinorantChecks

/-!
# The complete repeated-row family in the corrected four-row minorant

For x≤4 the literal objective is compactified to the closed cube and its
42,875 exact tensor coefficients are nonnegative. For x≥4, concavity in T
reduces to two explicit nonnegative endpoint values. This theorem covers
x=0,z=0,T=0,1 as well. It does not assert the compact-extremum reductions
needed to pass from arbitrary rows to this repeated-row family.
-/

namespace DittertRybin
open scoped BigOperators
open Certificates Certificates.FourRowMinorant

/-- Every coefficient is nonnegative after its positive common denominator is restored. -/
theorem fourRow_compactPowerValue_nonneg {X T Z : ℝ}
    (hX : 0 ≤ X ∧ X ≤ 1) (hT : 0 ≤ T ∧ T ≤ 1) (hZ : 0 ≤ Z ∧ Z ≤ 1) :
    0 ≤ compactPowerValue X T Z := by
  rw [compactPowerValue_bernstein]
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  have hc : 0 ≤ compactBernsteinCoefficient i j k := by
    rw [compactBernsteinCoefficient_eq_numerator]
    exact div_nonneg (by exact_mod_cast compactBernsteinNumerator_nonneg i j k) (by norm_num)
  exact mul_nonneg (mul_nonneg (mul_nonneg hc
    (bernsteinWeight_nonneg _ _ hX.1 hX.2)) (bernsteinWeight_nonneg _ _ hT.1 hT.2))
      (bernsteinWeight_nonneg _ _ hZ.1 hZ.2)

/-- The semantic compactification identity, proved directly from the literal source formula. -/
theorem fourRowRepeatedMinorant_compactification (x z T : ℝ) (hz : 1+z ≠ 0) :
    fourRowRepeatedMinorant x z T =
      (1+z)^2*compactPowerValue (x/4) T (z/(1+z)) := by
  norm_num [fourRowRepeatedMinorant,compactPowerValue,compactPowerCoefficient,Fin.sum_univ_succ]
  field_simp
  ring

theorem fourRowRepeatedMinorant_nonneg_small {x z T : ℝ}
    (hx : 0 ≤ x) (hx4 : x ≤ 4) (hz : 0 ≤ z) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ fourRowRepeatedMinorant x z T := by
  have hz1 : 0 < 1+z := by linarith
  have hX : 0 ≤ x/4 ∧ x/4 ≤ 1 := by constructor <;> linarith
  have hZ : 0 ≤ z/(1+z) ∧ z/(1+z) ≤ 1 := by
    exact ⟨div_nonneg hz hz1.le,(div_le_one hz1).mpr (by linarith)⟩
  rw [fourRowRepeatedMinorant_compactification x z T hz1.ne']
  exact mul_nonneg (sq_nonneg _) (fourRow_compactPowerValue_nonneg hX ⟨hT,hT1⟩ hZ)

theorem fourRowRepeatedMinorant_nonneg_large {x z T : ℝ}
    (hx : 4 ≤ x) (hz : 0 ≤ z) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ fourRowRepeatedMinorant x z T := by
  have hx0 : 0 ≤ x := by linarith
  have hTm : 0 ≤ 1-T := by linarith
  have hx4 : 0 ≤ x-4 := by linarith
  have hid : fourRowRepeatedMinorant x z T =
      (1-T)*((x-z)^2+x+z)+T*(2*(1+z+z^2))+
        (x+2+z)*z*(x-4)*T*(1-T) := by
    unfold fourRowRepeatedMinorant
    ring
  rw [hid]
  positivity

/-- Closed-domain repeated-row theorem, including every zero and endpoint parameter. -/
theorem fourRowRepeatedMinorant_nonneg {x z T : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ fourRowRepeatedMinorant x z T := by
  by_cases hx4 : x ≤ 4
  · exact fourRowRepeatedMinorant_nonneg_small hx hx4 hz hT hT1
  · exact fourRowRepeatedMinorant_nonneg_large (by linarith) hz hT hT1

theorem fourRowMinorantHomogeneous_repeated_nonneg {x z T : ℝ}
    (hx : 0 ≤ x) (hz : 0 ≤ z) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ fourRowMinorantHomogeneous ![x,1,1,z] ![T,(1-T)/2,(1-T)/2,0] := by
  rw [fourRowMinorantHomogeneous_repeated]
  exact fourRowRepeatedMinorant_nonneg hx hz hT hT1

end DittertRybin
