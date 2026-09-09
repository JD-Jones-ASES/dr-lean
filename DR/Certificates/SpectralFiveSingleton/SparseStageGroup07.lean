import DR.Certificates.SpectralFiveSingletonSparseStageData

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 64000000

theorem node56_checked : SparsePolynomial.pow node21 3 = node56 := by
  decide +kernel

theorem node57_checked : SparsePolynomial.mul node55 node56 = node57 := by
  decide +kernel

theorem node58_checked : SparsePolynomial.mul node41 node10 = node58 := by
  decide +kernel

theorem node59_checked : SparsePolynomial.mul node58 node50 = node59 := by
  decide +kernel

theorem node60_checked : SparsePolynomial.mul node46 node48 = node60 := by
  decide +kernel

theorem node61_checked : SparsePolynomial.add node59 node60 = node61 := by
  decide +kernel

theorem node62_checked : SparsePolynomial.mul node57 node61 = node62 := by
  decide +kernel

theorem node63_checked : SparsePolynomial.constant (16 : ℚ) = node63 := by
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
