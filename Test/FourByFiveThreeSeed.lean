import DR.Certificates.FourByFiveThree

namespace DittertRybin.Certificates.Tests
open scoped BigOperators

-- Literal source numerators, including zero and negative coefficients.
example : fourByFiveThreeCoefficient 0=(27/40:ℚ) ∧ fourByFiveThreeCoefficient 56=0 ∧
    fourByFiveThreeCoefficient 92=(-13/20:ℚ) := by decide +kernel

-- Every formula-defined physical entry is equal to the compact checked lookup.
example (s : Fin 4) : fourByFiveThreeSeed s=fourByFiveThreeTableMatrix s :=
  fourByFiveThreeSeed_eq_table s

-- All four equal labels have the first catalogue pattern; a changed lookup is rejected.
example : fourTuplePatternIndex (![0,0,0,0] : Fin 4 → Fin 4)≠(1:Fin 15) := by
  decide +kernel

-- The closed real spectral floor applies to all four actual seeds.
example (s : Fin 4) (x : Fin 20 → ℝ) :
    (2/5:ℝ)*((∑ i,x i^2)-(∑ i,x i)^2/20)≤
      quadraticValue ((fourByFiveThreeSeed s).map (fun q : ℚ => (q:ℝ))) x :=
  fourByFiveThreeSeed_lower s x

-- Arbitrary ordered physical multiplier pairs are covered, including repetitions.
example (e f : Fin 20) (x : Fin 20 → ℝ) :
    (2/5:ℝ)*((∑ i,x i^2)-(∑ i,x i)^2/20)≤
      quadraticValue ((fourByFiveThreeMatrix e f).map (fun q : ℚ => (q:ℝ))) x :=
  fourByFiveThreeMatrix_lower e f x

-- A single changed diagonal entry breaks the full constant kernel.
example : (∑ j : Fin 20,(fourByFiveThreeSeed 0 0 j+(if j=0 then (1/200:ℚ) else 0)))≠0 := by
  rw [Finset.sum_add_distrib,(fourByFiveThreeMatrix_checks 0).2.2 0]
  norm_num

-- The centering mutation keeps the constant kernel but changes the point-mass quartic coefficient.
example : (∑ j,centeringMatrix 20 (0:Fin 20) j)=0 := by
  norm_num [centeringMatrix,Fin.sum_univ_succ]
example : fourByFiveThreeCoefficient 0+centeringMatrix 20 0 0≠(27/40:ℚ) := by decide +kernel

#print axioms fourByFiveThreeRowPatterns_checked
#print axioms fourByFiveThreeColPatterns_checked
#print axioms fourByFiveThreeSeed_eq_table
#print axioms fourByFiveThreeGram_valid
#print axioms fourByFiveThreeMatrix_checks
#print axioms fourByFiveThreeShift_posSemidef
#print axioms fourByFiveThreeMatrix_lower
end DittertRybin.Certificates.Tests
