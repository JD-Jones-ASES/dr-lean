import DR.Certificates.FiniteK4QuinticLocal
import DR.Certificates.FiniteK4QuinticChecks.Rows00To06
import DR.Certificates.FiniteK4QuinticChecks.Rows07To13

namespace DittertRybin.Tests
open Certificates
open scoped BigOperators

-- The actual monomial for five repetitions has multiplicity one and no successes.
example : finiteK4QuinticMultiplicity.get (finiteK4QuinticEquation 0 0)=1 ∧
    finiteK4QuinticSuccesses.get (finiteK4QuinticEquation 0 0)=0 := by decide +kernel

-- Any signed coefficient vector obeying that actual row gives the exact local identity.
example (alpha : ℝ) (coeff : Fin 407 → ℝ)
    (h : finiteK4QuinticRowValue coeff (finiteK4QuinticEquation 0 0)=alpha) :
    finiteK4TripleValue coeff (finiteK4PatternSample 0 0)=60*alpha := by
  have hm : finiteK4QuinticMultiplicity.get (finiteK4QuinticEquation 0 0)=1 := by decide +kernel
  have hs : finiteK4QuinticSuccesses.get (finiteK4QuinticEquation 0 0)=0 := by decide +kernel
  have he := finiteK4TripleValue_pattern_eq 0 0 (finiteK4QuinticPatternCheck00 0)
    (alpha := alpha) (coeff := coeff)
    (by simpa only [hm,hs,Nat.cast_one,Nat.cast_zero,one_mul,sub_zero] using h)
  have hz : (∑ a : Fin 5, finiteK4DeletedSuccess (fiveTuplePatterns 0) (fiveTuplePatterns 0) a)=0 := by
    decide +kernel
  have hzr := congrArg (fun k : Nat => (k : ℝ)) hz
  simp only [Nat.cast_sum,Nat.cast_zero] at hzr
  simpa only [hzr,mul_zero,sub_zero] using he

-- A second chosen row pattern also passes all actual column-pattern gates.
example : ∀ c : Fin 52, FiniteK4QuinticPatternCorrect 7 c := finiteK4QuinticPatternCheck07

#print axioms finiteK4QuinticOrderedRole
#print axioms finiteK4TripleValue_pattern_eq
#print axioms finiteK4TripleValue_congr
#print axioms finiteK4TripleValue_eq_of_pattern
end DittertRybin.Tests
