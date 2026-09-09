import DR.Rectangular.FourRowFiniteDiagonalKernel
import DR.Rectangular.FourRowFiniteData50

namespace DittertRybin.Tests
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

example : fourRowFiniteDiagonalKernelPower fourRowFiniteFamilyNumerator50 50
    ⟨0,by change 0 < 16; decide⟩ 0 = 0 := by
  decide +kernel

example : fourRowFiniteDiagonalKernelPower fourRowFiniteFamilyNumerator50 50
    ⟨15,by change 15 < 16; decide⟩ 8 = 0 := by
  decide +kernel

example : fourRowFiniteDiagonalKernelPower fourRowFiniteFamilyNumerator50 50
    ⟨15,by change 15 < 16; decide⟩ 4 = 0 := by
  decide +kernel

end DittertRybin.Tests
