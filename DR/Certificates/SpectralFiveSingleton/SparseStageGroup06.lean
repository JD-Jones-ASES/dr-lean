import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node48_checked : SparsePolynomial.pow node47 2 = node48 := by
  decide +kernel

theorem node49_checked : SparsePolynomial.mul node48 node10 = node49 := by
  decide +kernel

theorem node50_checked : SparsePolynomial.add node09 node08 = node50 := by
  decide +kernel

theorem node51_checked : SparsePolynomial.mul node49 node50 = node51 := by
  decide +kernel

theorem node52_checked : SparsePolynomial.constant (5 : ℚ) = node52 := by
  decide +kernel

theorem node53_checked : SparsePolynomial.add node52 node15 = node53 := by
  decide +kernel

theorem node54_checked : SparsePolynomial.constant (16384 : ℚ) = node54 := by
  decide +kernel

theorem node55_checked : SparsePolynomial.mul node53 node54 = node55 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
