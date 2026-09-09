import DR.Certificates.SpectralFiveSingletonSparseSource
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup00
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup01
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup02
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup03
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup04
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup05
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup06
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup07
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup08
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup09
import DR.Certificates.SpectralFiveSingleton.SparseStageGroup10

namespace DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

theorem uPolynomial_checked : SparseSource.uPolynomial = node04 := by
  unfold SparseSource.uPolynomial
  simp only [node00_checked, node01_checked, node02_checked, node03_checked, node04_checked]

theorem vPolynomial_checked : SparseSource.vPolynomial = node08 := by
  unfold SparseSource.vPolynomial
  simp only [node01_checked, node05_checked, node06_checked, node07_checked, node08_checked]

theorem lowerPolynomial_checked : SparseSource.lowerPolynomial = node10 := by
  unfold SparseSource.lowerPolynomial
  simp only [node00_checked, node01_checked, node02_checked, node09_checked, node10_checked]

theorem qPolynomial_checked : SparseSource.qPolynomial = node11 := by
  unfold SparseSource.qPolynomial
  simp only [node01_checked, node09_checked, node11_checked]

theorem heightPolynomial_checked : SparseSource.heightPolynomial = node12 := by
  unfold SparseSource.heightPolynomial
  simp only [node01_checked, node05_checked, node06_checked, node09_checked, node12_checked]

theorem energyPolynomial_checked : SparseSource.energyPolynomial = node18 := by
  unfold SparseSource.energyPolynomial
  rw [show ((1 - 24 / 625) / 5 : ℚ) = 601 / 3125 by norm_num]
  simp only [heightPolynomial_checked]
  simp only [node01_checked, node13_checked, node14_checked, node15_checked, node16_checked, node17_checked, node18_checked]

theorem denominatorPolynomial_checked : SparseSource.denominatorPolynomial = node21 := by
  unfold SparseSource.denominatorPolynomial
  simp only [energyPolynomial_checked, qPolynomial_checked]
  simp only [node19_checked, node20_checked, node21_checked]

theorem crossingPolynomial_checked : SparseSource.crossingPolynomial = node25 := by
  unfold SparseSource.crossingPolynomial
  simp only [energyPolynomial_checked, qPolynomial_checked]
  simp only [node22_checked, node23_checked, node24_checked, node25_checked]

theorem anPolynomial_checked : SparseSource.anPolynomial = node30 := by
  unfold SparseSource.anPolynomial
  simp only [crossingPolynomial_checked, denominatorPolynomial_checked, uPolynomial_checked, vPolynomial_checked]
  simp only [node22_checked, node26_checked, node27_checked, node28_checked, node29_checked, node30_checked]

theorem snPolynomial_checked : SparseSource.snPolynomial = node35 := by
  unfold SparseSource.snPolynomial
  simp only [crossingPolynomial_checked, denominatorPolynomial_checked, uPolynomial_checked, vPolynomial_checked]
  simp only [node22_checked, node26_checked, node31_checked, node32_checked, node33_checked, node34_checked, node35_checked]

theorem rnPolynomial_checked : SparseSource.rnPolynomial = node41 := by
  unfold SparseSource.rnPolynomial
  simp only [crossingPolynomial_checked, denominatorPolynomial_checked, uPolynomial_checked, vPolynomial_checked]
  simp only [node22_checked, node26_checked, node36_checked, node37_checked, node38_checked, node39_checked, node40_checked, node41_checked]

theorem cnPolynomial_checked : SparseSource.cnPolynomial = node46 := by
  unfold SparseSource.cnPolynomial
  simp only [crossingPolynomial_checked, denominatorPolynomial_checked, lowerPolynomial_checked, uPolynomial_checked, vPolynomial_checked]
  simp only [node22_checked, node26_checked, node42_checked, node43_checked, node44_checked, node45_checked, node46_checked]

theorem commonPolynomial_checked : SparseSource.commonPolynomial = node51 := by
  unfold SparseSource.commonPolynomial
  simp only [lowerPolynomial_checked, uPolynomial_checked, vPolynomial_checked]
  simp only [node09_checked, node47_checked, node48_checked, node49_checked, node50_checked, node51_checked]

theorem enPolynomial_checked : SparseSource.enPolynomial = node74 := by
  unfold SparseSource.enPolynomial
  simp only [cnPolynomial_checked, commonPolynomial_checked, denominatorPolynomial_checked, lowerPolynomial_checked, rnPolynomial_checked, snPolynomial_checked, uPolynomial_checked, vPolynomial_checked]
  simp only [node01_checked, node09_checked, node15_checked, node47_checked, node48_checked, node50_checked, node52_checked, node53_checked, node54_checked, node55_checked, node56_checked, node57_checked, node58_checked, node59_checked, node60_checked, node61_checked, node62_checked, node63_checked, node64_checked, node65_checked, node66_checked, node67_checked, node68_checked, node69_checked, node70_checked, node71_checked, node72_checked, node73_checked, node74_checked]

theorem singletonPolynomial_checked : SparseSource.singletonPolynomial = node83 := by
  unfold SparseSource.singletonPolynomial
  simp only [anPolynomial_checked, commonPolynomial_checked, denominatorPolynomial_checked, enPolynomial_checked]
  simp only [node01_checked, node13_checked, node15_checked, node52_checked, node53_checked, node63_checked, node64_checked, node65_checked, node75_checked, node76_checked, node77_checked, node78_checked, node79_checked, node80_checked, node81_checked, node82_checked, node83_checked]

theorem scaledSingletonPolynomial_checked : SparseSource.scaledSingletonPolynomial = node85 := by
  unfold SparseSource.scaledSingletonPolynomial
  simp only [singletonPolynomial_checked]
  simp only [SparseSource.singletonScale, node84_checked, node85_checked]

end DittertRybin.Certificates.SpectralFiveSingleton.SparseStages
