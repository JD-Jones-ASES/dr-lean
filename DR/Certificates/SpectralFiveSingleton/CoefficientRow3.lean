import DR.Certificates.SpectralFiveSingletonCoefficientDefinitions

namespace DittertRybin.Certificates.SpectralFiveSingleton
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem singletonCoefficientMatch_30 : singletonCoefficientMatch 3 0 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_31 : singletonCoefficientMatch 3 1 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_32 : singletonCoefficientMatch 3 2 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_33 : singletonCoefficientMatch 3 3 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_34 : singletonCoefficientMatch 3 4 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_35 : singletonCoefficientMatch 3 5 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_36 : singletonCoefficientMatch 3 6 := by
  unfold singletonCoefficientMatch
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton
