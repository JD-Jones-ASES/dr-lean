import DR.Rectangular.FourRowFiniteData50
import DR.Rectangular.FourRowFiniteDataRows

namespace DittertRybin

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourRowFinite50_coefficient_identities : ∀ e : Fin 84,
    (fourRowFiniteCoefficientRows e).Valid 50 fourRowFiniteFamilyNumerator50 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 32000000 in
theorem fourRowFinite50_kernel_identities : ∀ e : Fin 65,
    fourRowFiniteKernelValid (fourRowFiniteKernelRows e) 50 fourRowFiniteFamilyNumerator50 := by
  decide +kernel

end DittertRybin
