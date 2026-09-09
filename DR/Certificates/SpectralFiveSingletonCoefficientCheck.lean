import DR.Certificates.SpectralFiveSingleton.CoefficientRow0
import DR.Certificates.SpectralFiveSingleton.CoefficientRow1
import DR.Certificates.SpectralFiveSingleton.CoefficientRow2
import DR.Certificates.SpectralFiveSingleton.CoefficientRow3
import DR.Certificates.SpectralFiveSingleton.CoefficientRow4
import DR.Certificates.SpectralFiveSingleton.CoefficientRow5
import DR.Certificates.SpectralFiveSingleton.CoefficientRow6
import DR.Certificates.SpectralFiveSingleton.CoefficientRow7

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section

theorem singletonCoefficientMatch_all (i : Fin 8) (j : Fin 7) : singletonCoefficientMatch i j := by
  fin_cases i <;> fin_cases j
  · exact singletonCoefficientMatch_00
  · exact singletonCoefficientMatch_01
  · exact singletonCoefficientMatch_02
  · exact singletonCoefficientMatch_03
  · exact singletonCoefficientMatch_04
  · exact singletonCoefficientMatch_05
  · exact singletonCoefficientMatch_06
  · exact singletonCoefficientMatch_10
  · exact singletonCoefficientMatch_11
  · exact singletonCoefficientMatch_12
  · exact singletonCoefficientMatch_13
  · exact singletonCoefficientMatch_14
  · exact singletonCoefficientMatch_15
  · exact singletonCoefficientMatch_16
  · exact singletonCoefficientMatch_20
  · exact singletonCoefficientMatch_21
  · exact singletonCoefficientMatch_22
  · exact singletonCoefficientMatch_23
  · exact singletonCoefficientMatch_24
  · exact singletonCoefficientMatch_25
  · exact singletonCoefficientMatch_26
  · exact singletonCoefficientMatch_30
  · exact singletonCoefficientMatch_31
  · exact singletonCoefficientMatch_32
  · exact singletonCoefficientMatch_33
  · exact singletonCoefficientMatch_34
  · exact singletonCoefficientMatch_35
  · exact singletonCoefficientMatch_36
  · exact singletonCoefficientMatch_40
  · exact singletonCoefficientMatch_41
  · exact singletonCoefficientMatch_42
  · exact singletonCoefficientMatch_43
  · exact singletonCoefficientMatch_44
  · exact singletonCoefficientMatch_45
  · exact singletonCoefficientMatch_46
  · exact singletonCoefficientMatch_50
  · exact singletonCoefficientMatch_51
  · exact singletonCoefficientMatch_52
  · exact singletonCoefficientMatch_53
  · exact singletonCoefficientMatch_54
  · exact singletonCoefficientMatch_55
  · exact singletonCoefficientMatch_56
  · exact singletonCoefficientMatch_60
  · exact singletonCoefficientMatch_61
  · exact singletonCoefficientMatch_62
  · exact singletonCoefficientMatch_63
  · exact singletonCoefficientMatch_64
  · exact singletonCoefficientMatch_65
  · exact singletonCoefficientMatch_66
  · exact singletonCoefficientMatch_70
  · exact singletonCoefficientMatch_71
  · exact singletonCoefficientMatch_72
  · exact singletonCoefficientMatch_73
  · exact singletonCoefficientMatch_74
  · exact singletonCoefficientMatch_75
  · exact singletonCoefficientMatch_76

end
end DittertRybin.Certificates.SpectralFiveSingleton
