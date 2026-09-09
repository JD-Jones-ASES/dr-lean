import DR.Certificates.FiniteK4FixedSeedEquations
import DR.Certificates.FiniteK4QuinticIdentity

/-! The literal fixed seeds satisfy the physical quintic identities at the
sharp uniform values. Matrix positivity and constant kernels are separate. -/
namespace DittertRybin.Certificates

theorem finiteK4Fixed5_uniform_value : uniformSeparationValue 5 5 4 = 5424/15625 := by
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

theorem finiteK4Fixed20_uniform_value : uniformSeparationValue 20 20 4 = 14805351/16000000 := by
  norm_num [uniformSeparationValue, distinctUniformProbability, Nat.descFactorial]

theorem finiteK4Fixed5_sharp_equations :
    FiniteK4CoefficientEquations (uniformSeparationValue 5 5 4)
      (fun k => (finiteK4Fixed5Coefficient k : ℝ)) := by
  rw [finiteK4Fixed5_uniform_value]
  exact finiteK4Fixed5_equations

theorem finiteK4Fixed20_sharp_equations :
    FiniteK4CoefficientEquations (uniformSeparationValue 20 20 4)
      (fun k => (finiteK4Fixed20Coefficient k : ℝ)) := by
  rw [finiteK4Fixed20_uniform_value]
  exact finiteK4Fixed20_equations

end DittertRybin.Certificates
