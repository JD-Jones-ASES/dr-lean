import DR.Certificates.FiniteK4FixedSeedData
import DR.Certificates.FiniteK4QuinticLocal

/-! Exact rational gates for the 5×5 and 20×20 fixed seeds. All 91 universal
coefficient equations are checked in the kernel and transported to ℝ. This
module supplies polynomial identities only; matrix positivity is separate. -/
namespace DittertRybin.Certificates
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

/-- The actual padded sparse quintic equation over exact rationals. -/
def FiniteK4RationalCoefficientEquations (alpha : ℚ) (coeff : Fin 407 → ℚ) : Prop :=
  ∀ a : Fin 91, (∑ k : Fin 10,
    ((finiteK4QuinticTerm a k).2 : ℚ) * coeff (finiteK4QuinticTerm a k).1) =
    (finiteK4QuinticMultiplicity.get a : ℚ) * alpha - (finiteK4QuinticSuccesses.get a : ℚ)

instance (alpha : ℚ) (coeff : Fin 407 → ℚ) :
    Decidable (FiniteK4RationalCoefficientEquations alpha coeff) := by
  unfold FiniteK4RationalCoefficientEquations
  infer_instance

/-- Exact rational coefficient equations imply the original real equations. -/
theorem FiniteK4RationalCoefficientEquations.cast {alpha : ℚ} {coeff : Fin 407 → ℚ}
    (h : FiniteK4RationalCoefficientEquations alpha coeff) :
    FiniteK4CoefficientEquations (alpha : ℝ) (fun k => (coeff k : ℝ)) := by
  intro a
  unfold finiteK4QuinticRowValue
  have he := congrArg (fun x : ℚ => (x : ℝ)) (h a)
  push_cast at he
  exact he

theorem finiteK4Fixed5_rational_equations :
    FiniteK4RationalCoefficientEquations finiteK4Fixed5Alpha finiteK4Fixed5Coefficient := by
  intro a
  fin_cases a <;> decide +kernel

theorem finiteK4Fixed20_rational_equations :
    FiniteK4RationalCoefficientEquations finiteK4Fixed20Alpha finiteK4Fixed20Coefficient := by
  intro a
  fin_cases a <;> decide +kernel

theorem finiteK4Fixed5_equations :
    FiniteK4CoefficientEquations (5424/15625)
      (fun k => (finiteK4Fixed5Coefficient k : ℝ)) := by
  convert finiteK4Fixed5_rational_equations.cast using 1
  norm_num [finiteK4Fixed5Alpha]

theorem finiteK4Fixed20_equations :
    FiniteK4CoefficientEquations (14805351/16000000)
      (fun k => (finiteK4Fixed20Coefficient k : ℝ)) := by
  convert finiteK4Fixed20_rational_equations.cast using 1
  norm_num [finiteK4Fixed20Alpha]

end DittertRybin.Certificates
