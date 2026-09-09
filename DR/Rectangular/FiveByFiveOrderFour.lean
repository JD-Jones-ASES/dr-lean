import DR.Certificates.FiniteK4FixedSoundness
import DR.Certificates.FiniteK4FixedSeedProbability
import DR.Certificates.FiniteK4FixedChecked5

/-! The sharp four-sample theorem on the entire 5×5 probability simplex.
The literal ten-seed certificates certify the physical quintic identity,
including its equality case and boards with zero cells. -/
namespace DittertRybin
open Certificates

theorem uniform_maximum_five_by_five_order_four : UniformMaximizer 5 5 4 :=
  finiteK4Fixed_uniformMaximizer (by decide) (by decide)
    (fun k => (finiteK4Fixed5Coefficient k : ℝ)) finiteK4Fixed5_sharp_equations
    finiteK4Fixed5_full_kernel_real finiteK4Fixed5_principal_posDef
    finiteK4Fixed5_row_posDef finiteK4Fixed5_column_posDef finiteK4Fixed5_interaction_posDef

theorem fiveByFive_orderFour_closed_simplex (P : Board 5 5) (hP : IsProbability P) :
    separationProbability P 4 ≤ 5424/15625 ∧
      (separationProbability P 4 = 5424/15625 ↔ P = uniformBoard 5 5) := by
  simpa only [finiteK4Fixed5_uniform_value] using
    uniform_maximum_five_by_five_order_four P hP

end DittertRybin
