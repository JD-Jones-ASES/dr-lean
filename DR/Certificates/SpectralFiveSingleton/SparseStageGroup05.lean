import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node40_checked : SparsePolynomial.mul node26 node39 = node40 := by
  decide +kernel

theorem node41_checked : SparsePolynomial.sub node40 node25 = node41 := by
  decide +kernel

theorem node42_checked : SparsePolynomial.mul node22 node10 = node42 := by
  decide +kernel

theorem node43_checked : SparsePolynomial.add node42 node04 = node43 := by
  decide +kernel

theorem node44_checked : SparsePolynomial.add node43 node08 = node44 := by
  decide +kernel

theorem node45_checked : SparsePolynomial.mul node26 node44 = node45 := by
  decide +kernel

theorem node46_checked : SparsePolynomial.sub node45 node25 = node46 := by
  decide +kernel

theorem node47_checked : SparsePolynomial.sub node09 node04 = node47 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
