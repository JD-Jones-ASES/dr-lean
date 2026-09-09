import DR.Certificates.SpectralFiveSingletonCoefficientDefinitions

namespace DittertRybin.Certificates.SpectralFiveSingleton
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem singletonCoefficientMatch_00 : singletonCoefficientMatch 0 0 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_01 : singletonCoefficientMatch 0 1 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_02 : singletonCoefficientMatch 0 2 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_03 : singletonCoefficientMatch 0 3 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_04 : singletonCoefficientMatch 0 4 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_05 : singletonCoefficientMatch 0 5 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_06 : singletonCoefficientMatch 0 6 := by
  unfold singletonCoefficientMatch
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton
