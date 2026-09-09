import DR.Certificates.FiniteK3QuarticLocal

namespace DittertRybin.Certificates
open scoped BigOperators

example : finiteK3MultiplierWeight (![0,0,1,2] : Fin 4 → Nat)
    (![0,1,2,3] : Fin 4 → Nat) = 1 := by decide
example : finiteK3MultiplierWeight (![7,7,9,10] : Fin 4 → Nat)
    (![5,5,6,7] : Fin 4 → Nat) = 2 := by decide

-- Each axis separately suffices. Inclusive OR counts simultaneous success once.
example : finiteK3DeletedSuccess (![0,1,2,0] : Fin 4 → Nat) (fun _ => (0 : Nat)) 3 = 1 := by decide
example : finiteK3DeletedSuccess (fun _ => (0 : Nat)) (![0,1,2,0] : Fin 4 → Nat) 3 = 1 := by decide
example : finiteK3DeletedSuccess (![0,1,2,0] : Fin 4 → Nat)
    (![0,1,2,0] : Fin 4 → Nat) 3 = 1 := by decide
example : finiteK3DeletedSuccess (![0,0,1,2] : Fin 4 → Nat)
    (![0,1,0,2] : Fin 4 → Nat) 3 = 0 := by decide

-- The all-equal monomial retains all six pair choices, each of weight two.
example : finiteK3PatternPairCoefficient 0 0 0 = 12 := by decide +kernel
example : finiteK3QuarticMultiplicity.get (finiteK3PatternEquation 0 0) = 1 := by decide

-- Corrupting the constant monomial cannot pass the full coefficient equations.
example : ¬FiniteK3CoefficientEquations 1 (fun _ => 0) := by
  intro h
  have h0 := h 0
  rw [show finiteK3QuarticMultiplicity.get 0 = 1 by decide,
    show finiteK3QuarticSuccesses.get 0 = 0 by decide] at h0
  norm_num at h0

example {α β : Type*} [DecidableEq α] [DecidableEq β]
    (alpha : ℝ) (coeff : Fin 93 → ℝ) (h : FiniteK3CoefficientEquations alpha coeff)
    (r : Fin 4 → α) (c : Fin 4 → β) :
    finiteK3PairValue coeff r c = 12*alpha-3*(∑ a, (finiteK3DeletedSuccess r c a : ℝ)) :=
  finiteK3PairValue_eq h r c

#print axioms finiteK3PairPattern_compression
#print axioms finiteK3PatternPairData
#print axioms finiteK3PatternPairCoefficient_identity
#print axioms finiteK3PatternDeletedSuccess_identity
#print axioms finiteK3PairValue_pattern_eq
#print axioms finiteK3PairValue_eq

end DittertRybin.Certificates
