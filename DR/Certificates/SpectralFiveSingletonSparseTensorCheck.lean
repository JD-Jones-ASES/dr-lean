import DR.Certificates.SpectralFiveSingletonSparseStageData
import DR.Certificates.SpectralFiveSingletonPowerData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem final_tensor_checked : node85 =
    SparsePolynomial.fromTensor singletonPowerCoefficients := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
