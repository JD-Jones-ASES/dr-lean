import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node24_checked : SparsePolynomial.sub node23 node18 = node24 := by
  decide +kernel

theorem node25_checked : SparsePolynomial.mul node18 node24 = node25 := by
  decide +kernel

theorem node26_checked : SparsePolynomial.mul node22 node21 = node26 := by
  decide +kernel

theorem node27_checked : SparsePolynomial.add node22 node08 = node27 := by
  decide +kernel

theorem node28_checked : SparsePolynomial.sub node27 node04 = node28 := by
  decide +kernel

theorem node29_checked : SparsePolynomial.mul node26 node28 = node29 := by
  decide +kernel

theorem node30_checked : SparsePolynomial.sub node29 node25 = node30 := by
  decide +kernel

theorem node31_checked : SparsePolynomial.constant (8 : ℚ) = node31 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
