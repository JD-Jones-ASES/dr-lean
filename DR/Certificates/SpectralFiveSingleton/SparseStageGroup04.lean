import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node32_checked : SparsePolynomial.add node31 node04 = node32 := by
  decide +kernel

theorem node33_checked : SparsePolynomial.sub node32 node08 = node33 := by
  decide +kernel

theorem node34_checked : SparsePolynomial.mul node26 node33 = node34 := by
  decide +kernel

theorem node35_checked : SparsePolynomial.sub node34 node25 = node35 := by
  decide +kernel

theorem node36_checked : SparsePolynomial.constant (3 : ℚ) = node36 := by
  decide +kernel

theorem node37_checked : SparsePolynomial.mul node36 node04 = node37 := by
  decide +kernel

theorem node38_checked : SparsePolynomial.sub node22 node37 = node38 := by
  decide +kernel

theorem node39_checked : SparsePolynomial.sub node38 node08 = node39 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
