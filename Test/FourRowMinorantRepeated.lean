import DR.Rectangular.FourRowMinorantRepeated

namespace DittertRybin.Test
open scoped BigOperators
open Certificates Certificates.FourRowMinorant

-- The actual repeated-row homogeneous excess, including its closed boundary.
example (x z T : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    0 ≤ fourRowMinorantHomogeneous ![x,1,1,z] ![T,(1-T)/2,(1-T)/2,0] :=
  fourRowMinorantHomogeneous_repeated_nonneg hx hz hT hT1

-- Exact endpoint and transition identities, rather than sampled values.
example (x z : ℝ) : fourRowRepeatedMinorant x z 0 = (x-z)^2+x+z := by
  unfold fourRowRepeatedMinorant
  ring
example (x z : ℝ) : fourRowRepeatedMinorant x z 1 = 2*(1+z+z^2) := by
  unfold fourRowRepeatedMinorant
  ring
example (z T : ℝ) : fourRowRepeatedMinorant 4 z T =
    (1-T)*fourRowRepeatedMinorant 4 z 0+T*fourRowRepeatedMinorant 4 z 1 := by
  unfold fourRowRepeatedMinorant
  ring
example : fourRowRepeatedMinorant 0 0 0 = 0 := by norm_num [fourRowRepeatedMinorant]
example (X T : ℝ) (hX : 0 ≤ X ∧ X ≤ 1) (hT : 0 ≤ T ∧ T ≤ 1) :
    0 ≤ compactPowerValue X T 1 := fourRow_compactPowerValue_nonneg hX hT (by norm_num)

-- The stated minimum is attained exactly, and its denominator is restored correctly.
example : compactBernsteinNumerator 8 12 21 = 6323724 := by decide +kernel
example : compactBernsteinCoefficient 8 12 21 = (5323:ℝ)/1188946 := by
  rw [compactBernsteinCoefficient_eq_numerator]
  norm_num [compactBernsteinNumerator,degree34MomentNumerator]
example : Fintype.card (Fin 35 × Fin 35 × Fin 35) = 42875 := coefficient_count

-- Degree32 fails this same power-to-Bernstein formula at the literal index (7,11,20).
example : (∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
    (compactPowerCoefficient a b c:ℚ)*((7:ℕ).choose a:ℚ)/((32:ℕ).choose a:ℚ)*
      ((11:ℕ).choose b:ℚ)/((32:ℕ).choose b:ℚ)*
        ((20:ℕ).choose c:ℚ)/((32:ℕ).choose c:ℚ)) = -(12863:ℚ)/15252992 := by
  decide +kernel

-- The cleared compactification denominator is necessary even at a small exact point.
example : fourRowRepeatedMinorant 4 1 1 = 6 := by norm_num [fourRowRepeatedMinorant]
example : compactPowerValue 1 1 (1/2) = (3:ℝ)/2 := by
  norm_num [compactPowerValue,compactPowerCoefficient,Fin.sum_univ_succ]
example : fourRowRepeatedMinorant 4 1 1 ≠ compactPowerValue 1 1 (1/2) := by
  norm_num [fourRowRepeatedMinorant,compactPowerValue,compactPowerCoefficient,Fin.sum_univ_succ]

#print axioms compactBernsteinNumerator_nonneg
#print axioms compactBernsteinNumerator_margin
#print axioms compactPowerValue_bernstein
#print axioms fourRowRepeatedMinorant_compactification
#print axioms fourRowRepeatedMinorant_nonneg
#print axioms fourRowMinorantHomogeneous_repeated_nonneg
#print axioms fourRowMinorantHomogeneous_eq_gap

end DittertRybin.Test
