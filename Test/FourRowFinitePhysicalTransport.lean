import DR.Rectangular.FourRowFinitePhysicalCriterion

namespace DittertRybin.Tests
open Certificates
noncomputable section

-- All ordinary labels are actual host labels, not sample-dependent aliases.
example : fourRowFinitePhysicalAxisEquiv (by decide : 0 ≤ 3) (.inr (2 : Fin 3)) =
    (2 : Fin 3) := rfl

example : fourRowFiniteSeedPhysicalEquiv (by decide : 3 ≤ 4) (by decide : 3 ≤ 5) 9
    (.inr (0 : Fin 1),.inr (1 : Fin 2)) = ((3 : Fin 4),(4 : Fin 5)) := rfl

-- With no ordinary row or column, the same physical entry identity remains exact.
example (h : ℕ → ℝ) :
    (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k))
      (finiteTriplePhysicalSeed (by decide : 3 ≤ 3) (by decide : 3 ≤ 3) 9)).submatrix
      (fourRowFiniteSeedPhysicalEquiv (by decide) (by decide) 9)
      (fourRowFiniteSeedPhysicalEquiv (by decide) (by decide) 9) =
      twoAxisOrdinaryMatrix (fourRowFiniteSeedRelationKernel 9 h) :=
  fourRowFiniteSeedMatrix_physical (by decide) (by decide) 9 h

example (h : ℕ → ℝ) :
    (finiteK4Entry (fun k => h (finiteK4RoleKeys.get k))
      (finiteTriplePhysicalSeed (by decide : 3 ≤ 5) (by decide : 3 ≤ 20) 4)).submatrix
      (fourRowFiniteSeedPhysicalEquiv (by decide) (by decide) 4)
      (fourRowFiniteSeedPhysicalEquiv (by decide) (by decide) 4) =
      twoAxisOrdinaryMatrix (fourRowFiniteSeedRelationKernel 4 h) :=
  fourRowFiniteSeedMatrix_physical (by decide) (by decide) 4 h

-- The physical identification makes no positivity claim for arbitrary data.
example : finiteK4Entry (fun _ => -2 : Fin 407 → ℝ)
    (finiteTriplePhysicalSeed (by decide : 3 ≤ 3) (by decide : 3 ≤ 3) 9)
    (0,0) (1,1) = -2 := rfl

#print axioms fourRowFinitePhysicalAxisEquiv
#print axioms fourRowFiniteSeedPhysicalEquiv_seed
#print axioms fourRowFiniteSeedRole_physical
#print axioms fourRowFiniteSeedMatrix_physical
#print axioms fourRowFiniteSeedMatrix_criterion
#print axioms fourRowFinite_psd_constant_kernel_smul

end
end DittertRybin.Tests
