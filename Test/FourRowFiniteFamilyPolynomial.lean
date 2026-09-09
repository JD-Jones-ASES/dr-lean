import DR.Rectangular.FourRowFiniteFamilyPolynomial

namespace DittertRybin
open Certificates
noncomputable section

example : fourRowFiniteRoleLookup 0 = 0 := by decide +kernel

example : fourRowFiniteRoleLookup
    (finiteK4RoleKeys.get (finiteK4FourRowRoleIndices.get 390)) ≠ 389 := by
  rw [fourRowFiniteRoleLookup_key]
  decide

-- Negative and zero coefficients are admitted; evaluation is an exact identity for all real u.
example (key : ℕ) (u : ℝ) : rationalEval (fun _ => u)
    (fourRowFiniteFamilyRolePolynomial (fun _ => ![-2,0,0,0,0]) key) = -2 := by
  rw [fourRowFiniteFamilyRolePolynomial_eval]
  norm_num [fourRowFiniteNumeratorValue, Fin.sum_univ_succ]

example (key : ℕ) :
    (fourRowFiniteFamilyRolePolynomial (fun _ => ![0,0,0,0,0]) key).totalDegree = 0 := by
  simp [fourRowFiniteFamilyRolePolynomial, powerPolynomial, Fin.sum_univ_succ]

-- The physical catalogue conclusion carries no lower bound on the column count.
example {n : ℕ} (s : Fin 5 → Fin 4 × Fin n) :
    finiteK4FourRowRoleIndices.get (fourRowFiniteRoleLookup
      (finiteK4TupleRoleKey (fun i => ((s i).1.val, (s i).2.val)))) =
      finiteK4RoleIndex (fun i => ((s i).1.val, (s i).2.val)) :=
  fourRowFiniteRoleLookup_finFour s

#print axioms fourRowFiniteRoleLookup_key
#print axioms fourRowFiniteFamilyRolePolynomial_key
#print axioms fourRowFiniteFamilyRolePolynomial_eval
#print axioms fourRowFiniteFamilyRolePolynomial_totalDegree
#print axioms fourRowFiniteRoleLookup_tuple
#print axioms fourRowFiniteRoleLookup_finFour

end
end DittertRybin
