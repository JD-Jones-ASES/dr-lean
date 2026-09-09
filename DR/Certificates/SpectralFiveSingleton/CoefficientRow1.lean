import DR.Certificates.SpectralFiveSingletonCoefficientDefinitions

namespace DittertRybin.Certificates.SpectralFiveSingleton
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem singletonCoefficientMatch_10 : singletonCoefficientMatch 1 0 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_11 : singletonCoefficientMatch 1 1 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_12 : singletonCoefficientMatch 1 2 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_13 : singletonCoefficientMatch 1 3 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_14 : singletonCoefficientMatch 1 4 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_15 : singletonCoefficientMatch 1 5 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_16 : singletonCoefficientMatch 1 6 := by
  unfold singletonCoefficientMatch
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton
