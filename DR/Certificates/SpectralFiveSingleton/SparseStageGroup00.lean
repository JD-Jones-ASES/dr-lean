import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node00_checked : SparsePolynomial.constant ((23 : ℚ) / 50) = node00 := by
  decide +kernel

theorem node01_checked : SparsePolynomial.var 0 = node01 := by
  decide +kernel

theorem node02_checked : SparsePolynomial.mul node00 node01 = node02 := by
  decide +kernel

theorem node03_checked : SparsePolynomial.var 1 = node03 := by
  decide +kernel

theorem node04_checked : SparsePolynomial.mul node02 node03 = node04 := by
  decide +kernel

theorem node05_checked : SparsePolynomial.constant ((1 : ℚ) / 2) = node05 := by
  decide +kernel

theorem node06_checked : SparsePolynomial.mul node05 node01 = node06 := by
  decide +kernel

theorem node07_checked : SparsePolynomial.var 2 = node07 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
