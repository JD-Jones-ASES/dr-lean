import DR.Rectangular.FourRowFiniteData5
import DR.Rectangular.FourRowFiniteDataRows

namespace DittertRybin

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourRowFinite5_coefficient_identities : ∀ e : Fin 84,
    (fourRowFiniteCoefficientRows e).Valid 5 fourRowFiniteFamilyNumerator5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourRowFinite5_kernel_identities : ∀ e : Fin 65,
    fourRowFiniteKernelValid (fourRowFiniteKernelRows e) 5 fourRowFiniteFamilyNumerator5 := by
  decide +kernel

end DittertRybin
