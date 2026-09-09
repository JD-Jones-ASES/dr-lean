import DR.Certificates.SpectralFiveSingletonCoefficientDefinitions

namespace DittertRybin.Certificates.SpectralFiveSingleton
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem singletonCoefficientMatch_50 : singletonCoefficientMatch 5 0 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_51 : singletonCoefficientMatch 5 1 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_52 : singletonCoefficientMatch 5 2 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_53 : singletonCoefficientMatch 5 3 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_54 : singletonCoefficientMatch 5 4 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_55 : singletonCoefficientMatch 5 5 := by
  unfold singletonCoefficientMatch
  decide +kernel

theorem singletonCoefficientMatch_56 : singletonCoefficientMatch 5 6 := by
  unfold singletonCoefficientMatch
  decide +kernel

end DittertRybin.Certificates.SpectralFiveSingleton
