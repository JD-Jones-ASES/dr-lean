import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node16_checked : SparsePolynomial.mul node14 node15 = node16 := by
  decide +kernel

theorem node17_checked : SparsePolynomial.sub node13 node16 = node17 := by
  decide +kernel

theorem node18_checked : SparsePolynomial.mul node12 node17 = node18 := by
  decide +kernel

theorem node19_checked : SparsePolynomial.constant ((19 : ℚ) / 100) = node19 := by
  decide +kernel

theorem node20_checked : SparsePolynomial.mul node19 node11 = node20 := by
  decide +kernel

theorem node21_checked : SparsePolynomial.sub node20 node18 = node21 := by
  decide +kernel

theorem node22_checked : SparsePolynomial.constant (2 : ℚ) = node22 := by
  decide +kernel

theorem node23_checked : SparsePolynomial.mul node22 node11 = node23 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
