import DR.Certificates.FiniteK3EnvelopeIntegerEquations

namespace DittertRybin.Certificates.Tests

-- The common-denominator transfer retains the exact rational equations.
example (m n D : Nat) (A : ℤ) (c : Fin 93 → ℤ) (hD : 0<D)
    (hAlpha : finiteK3EnvelopeAlpha m n=(A:ℚ)/D)
    (h : FiniteK3EnvelopeIntegerEquations D A c) :
    FiniteK3EnvelopeEquations m n (fun i => (c i:ℚ)/D) :=
  finiteK3EnvelopeEquations_of_integer m n D A c hD hAlpha h

-- With denominator zero, trivial integer equations do not imply the intended rational identity.
example : FiniteK3EnvelopeIntegerEquations 0 0 (fun _ => 0) := by
  intro a
  simp only [mul_zero,Int.natCast_zero,Finset.sum_const_zero,sub_zero]
example : ¬FiniteK3EnvelopeEquations 4 6 (fun _ => (0:ℚ)/0) := by
  intro h
  have h0 := h 0
  have hm : finiteK3QuarticMultiplicity.get 0=1 := rfl
  have hs : finiteK3QuarticSuccesses.get 0=0 := rfl
  simp only [div_zero,mul_zero,Finset.sum_const_zero,hm,hs,Nat.cast_one,Nat.cast_zero,
    one_mul,sub_zero] at h0
  norm_num [finiteK3EnvelopeAlpha,Nat.descFactorial] at h0

#print axioms finiteK3EnvelopeEquations_of_integer
end DittertRybin.Certificates.Tests
