import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node72_checked : SparsePolynomial.mul node71 node51 = node72 := by
  decide +kernel

theorem node73_checked : SparsePolynomial.mul node72 node53 = node73 := by
  decide +kernel

theorem node74_checked : SparsePolynomial.sub node68 node73 = node74 := by
  decide +kernel

theorem node75_checked : SparsePolynomial.mul node30 node74 = node75 := by
  decide +kernel

theorem node76_checked : SparsePolynomial.constant (4 : ℚ) = node76 := by
  decide +kernel

theorem node77_checked : SparsePolynomial.mul node76 node21 = node77 := by
  decide +kernel

theorem node78_checked : SparsePolynomial.mul node13 node53 = node78 := by
  decide +kernel

theorem node79_checked : SparsePolynomial.sub node78 node15 = node79 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
