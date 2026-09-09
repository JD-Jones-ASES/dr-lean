import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node80_checked : SparsePolynomial.mul node77 node79 = node80 := by
  decide +kernel

theorem node81_checked : SparsePolynomial.mul node80 node65 = node81 := by
  decide +kernel

theorem node82_checked : SparsePolynomial.mul node81 node51 = node82 := by
  decide +kernel

theorem node83_checked : SparsePolynomial.sub node75 node82 = node83 := by
  decide +kernel

theorem node84_checked : SparsePolynomial.constant (727595761418342590332031250000000000000000000 : ℚ) = node84 := by
  decide +kernel

theorem node85_checked : SparsePolynomial.mul node84 node83 = node85 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
