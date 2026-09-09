import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node64_checked : SparsePolynomial.mul node63 node21 = node64 := by
  decide +kernel

theorem node65_checked : SparsePolynomial.pow node64 4 = node65 := by
  decide +kernel

theorem node66_checked : SparsePolynomial.mul node15 node65 = node66 := by
  decide +kernel

theorem node67_checked : SparsePolynomial.mul node66 node51 = node67 := by
  decide +kernel

theorem node68_checked : SparsePolynomial.sub node62 node67 = node68 := by
  decide +kernel

theorem node69_checked : SparsePolynomial.constant ((61 : ℚ) / 32) = node69 := by
  decide +kernel

theorem node70_checked : SparsePolynomial.pow node35 4 = node70 := by
  decide +kernel

theorem node71_checked : SparsePolynomial.mul node69 node70 = node71 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
