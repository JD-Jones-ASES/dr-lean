import DR.Certificates.FiniteK4FixedSoundness
import DR.Certificates.FiniteK4FixedSeedProbability
import DR.Certificates.FiniteK4FixedChecked20

/-! The sharp four-sample theorem on the entire 20×20 probability simplex,
from the literal ten-seed certificates and the physical quintic identity. -/
namespace DittertRybin
open Certificates

theorem uniform_maximum_twenty_by_twenty_order_four : UniformMaximizer 20 20 4 :=
  finiteK4Fixed_uniformMaximizer (by decide) (by decide)
    (fun k => (finiteK4Fixed20Coefficient k : ℝ)) finiteK4Fixed20_sharp_equations
    finiteK4Fixed20_full_kernel_real finiteK4Fixed20_principal_posDef
    finiteK4Fixed20_row_posDef finiteK4Fixed20_column_posDef finiteK4Fixed20_interaction_posDef

theorem twentyByTwenty_orderFour_closed_simplex (P : Board 20 20) (hP : IsProbability P) :
    separationProbability P 4 ≤ 14805351/16000000 ∧
      (separationProbability P 4 = 14805351/16000000 ↔ P = uniformBoard 20 20) := by
  simpa only [finiteK4Fixed20_uniform_value] using
    uniform_maximum_twenty_by_twenty_order_four P hP

end DittertRybin
