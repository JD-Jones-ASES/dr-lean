import DR.Rectangular.FourByFiveThreeGeometry

namespace DittertRybin.Tests

private def point : Board 4 5 := fun i j => if i.val=0 ∧ j.val=0 then 1 else 0

-- The extreme boundary probability keeps the exact Frobenius normalization 19/20.
example : IsProbability point ∧ fourByFiveThreeEnergy point=19/20 := by
  constructor
  · constructor
    · intro i j
      simp only [point]
      split_ifs <;> norm_num
    · simp only [totalMass,rowSum,point,Fin.sum_univ_succ]
      norm_num [Fin.ext_iff]
  · simp only [fourByFiveThreeEnergy,point,Fin.sum_univ_succ]
    norm_num [Fin.ext_iff]

example : fourByFiveThreeEnergy (0:Board 4 5)=1/20 := by
  norm_num [fourByFiveThreeEnergy]

-- The zero-distance characterization applies even before positivity and normalization.
example (P : Board 4 5) : fourByFiveThreeEnergy P=0 ↔ P=uniformBoard 4 5 :=
  fourByFiveThreeEnergy_eq_zero_iff P

example : separationProbability (uniformBoard 4 5) 3=(27/40:ℝ) :=
  fourByFiveThree_uniform_value

#print axioms fourByFiveThree_centered_sum
#print axioms fourByFiveThreeEnergy_eq_zero_iff
#print axioms fourByFiveThree_uniform_value
end DittertRybin.Tests
