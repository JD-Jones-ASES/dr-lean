import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node08_checked : SparsePolynomial.mul node06 node07 = node08 := by
  decide +kernel

theorem node09_checked : SparsePolynomial.constant (1 : ℚ) = node09 := by
  decide +kernel

theorem node10_checked : SparsePolynomial.sub node09 node02 = node10 := by
  decide +kernel

theorem node11_checked : SparsePolynomial.sub node09 node01 = node11 := by
  decide +kernel

theorem node12_checked : SparsePolynomial.add node09 node06 = node12 := by
  decide +kernel

theorem node13_checked : SparsePolynomial.constant ((24 : ℚ) / 625) = node13 := by
  decide +kernel

theorem node14_checked : SparsePolynomial.constant ((601 : ℚ) / 3125) = node14 := by
  decide +kernel

theorem node15_checked : SparsePolynomial.pow node01 2 = node15 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
