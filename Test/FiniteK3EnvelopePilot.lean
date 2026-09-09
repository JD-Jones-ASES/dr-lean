import DR.Certificates.FiniteK3Cases.M4N6
import DR.Certificates.FiniteK3Cases.M4N959

namespace DittertRybin.Certificates.Tests
open scoped BigOperators

-- All four actual seed blocks, kernels and quartic equations are covered at each endpoint.
example : FiniteK3EnvelopeValid 4 6 (by decide) FiniteK3Cases.C4N6.coeff := FiniteK3Cases.C4N6.valid
example : FiniteK3EnvelopeValid 4 959 (by decide) FiniteK3Cases.C4N959.coeff := FiniteK3Cases.C4N959.valid

-- The exact rational target value is the actual uniform probability value after casting.
example : finiteK3EnvelopeAlpha 4 6=(13/18:ℚ) := by decide +kernel
example (m n : Nat) : (finiteK3EnvelopeAlpha m n:ℝ)=uniformSeparationValue m n 3 :=
  finiteK3EnvelopeAlpha_cast m n

-- Each lookup equals the actual complete role map, with no coefficient restrictions.
example (coeff : Fin 93 → ℚ) (s : Fin 4) (a b : Fin 9 × Fin 4) :
    finiteK3EnvelopeEntry coeff s a b=finiteK3Entry coeff (0,0)
      ((finiteK3EnvelopeRowMode s).castLE (by decide),
       (finiteK3EnvelopeColMode s).castLE (by decide)) a b := finiteK3EnvelopeEntry_eq coeff s a b

-- A changed multiplicity in the aggregate block loses its prescribed kernel.
example : (∑ j,finiteK3EnvelopeFlatTableB FiniteK3Cases.C4N6.coeff 4 5 (by decide) 0 (4:Fin 8) j*
    finiteK3EnvelopeKernel 4 6 0 j)≠0 := by decide +kernel

-- A single changed source coefficient fails the actual quartic gate.
example : ¬FiniteK3EnvelopeEquations 4 6
    (fun k => FiniteK3Cases.C4N6.coeff k+(if k=0 then (1/200:ℚ) else 0)) := by
  decide +kernel

#print axioms finiteK3EnvelopeEntry_eq
#print axioms finiteK3EnvelopeH_eq_table
#print axioms finiteK3EnvelopeB_eq_table
#print axioms finiteK3EnvelopeFlatB_eq_table
#print axioms FiniteK3Cases.C4N6.valid
#print axioms FiniteK3Cases.C4N959.valid
end DittertRybin.Certificates.Tests
