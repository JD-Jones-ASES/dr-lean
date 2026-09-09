import DR.Certificates.FourByFiveThreeOrbits

namespace DittertRybin.Certificates.Tests

-- Each literal physical pair is assigned to its documented orbit without sorting labels.
example : fourByFiveThreePairType 14 14=0 ∧ fourByFiveThreePairType 14 10=1 ∧
    fourByFiveThreePairType 14 4=2 ∧ fourByFiveThreePairType 14 18=3 := by decide +kernel

example : fourByFiveThreePairPermutation 14 18 14=0 ∧
    fourByFiveThreePairPermutation 14 18 18=6 := by decide +kernel

-- The formula-defined physical matrix, not a sampled list of vectors, is a seed conjugate.
example (e f : Fin 20) :
    fourByFiveThreeMatrix e f=(fourByFiveThreeSeed (fourByFiveThreePairType e f)).submatrix
      (fourByFiveThreePairPermutation e f) (fourByFiveThreePairPermutation e f) :=
  fourByFiveThreeMatrix_conjugate e f

-- Reversing either role is valid, but exchanging the roles is not assumed.
example (e f a b : Fin 20) : fourByFiveThreeMatrix e f a b=fourByFiveThreeMatrix e f b a :=
  fourByFiveThreeMatrix_symmetric e f a b

#print axioms fourByFiveThreePairPermutation_first
#print axioms fourByFiveThreePairPermutation_second
#print axioms fourByFiveThreeMatrix_conjugate
end DittertRybin.Certificates.Tests
