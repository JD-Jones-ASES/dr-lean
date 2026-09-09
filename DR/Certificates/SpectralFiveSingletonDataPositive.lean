import DR.Certificates.SpectralFiveSingletonData

/-! Positivity of all 56 coefficient polynomials, with the entire closed t interval covered. -/

namespace DittertRybin.Certificates.SpectralFiveSingleton
noncomputable section

theorem blockPowerCoefficients_pos (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 9/20)
    (i : Fin 8) (j : Fin 7) :
    0 < rationalEval (fun _ : Fin 1 => t) (powerPolynomial (blockPowerCoefficients i j)) := by
  fin_cases i
  · fin_cases j
    · exact block00_pos t ht ht1
    · exact block01_pos t ht ht1
    · exact block02_pos t ht ht1
    · exact block03_pos t ht ht1
    · exact block04_pos t ht ht1
    · exact block05_pos t ht ht1
    · exact block06_pos t ht ht1
  · fin_cases j
    · exact block07_pos t ht ht1
    · exact block08_pos t ht ht1
    · exact block09_pos t ht ht1
    · exact block10_pos t ht ht1
    · exact block11_pos t ht ht1
    · exact block12_pos t ht ht1
    · exact block13_pos t ht ht1
  · fin_cases j
    · exact block14_pos t ht ht1
    · exact block15_pos t ht ht1
    · exact block16_pos t ht ht1
    · exact block17_pos t ht ht1
    · exact block18_pos t ht ht1
    · exact block19_pos t ht ht1
    · exact block20_pos t ht ht1
  · fin_cases j
    · exact block21_pos t ht ht1
    · exact block22_pos t ht ht1
    · exact block23_pos t ht ht1
    · exact block24_pos t ht ht1
    · exact block25_pos t ht ht1
    · exact block26_pos t ht ht1
    · exact block27_pos t ht ht1
  · fin_cases j
    · exact block28_pos t ht ht1
    · exact block29_pos t ht ht1
    · exact block30_pos t ht ht1
    · exact block31_pos t ht ht1
    · exact block32_pos t ht ht1
    · exact block33_pos t ht ht1
    · exact block34_pos t ht ht1
  · fin_cases j
    · exact block35_pos t ht ht1
    · exact block36_pos t ht ht1
    · exact block37_pos t ht ht1
    · exact block38_pos t ht ht1
    · exact block39_pos t ht ht1
    · exact block40_pos t ht ht1
    · exact block41_pos t ht ht1
  · fin_cases j
    · exact block42_pos t ht ht1
    · exact block43_pos t ht ht1
    · exact block44_pos t ht ht1
    · exact block45_pos t ht ht1
    · exact block46_pos t ht ht1
    · exact block47_pos t ht ht1
    · exact block48_pos t ht ht1
  · fin_cases j
    · exact block49_pos t ht ht1
    · exact block50_pos t ht ht1
    · exact block51_pos t ht ht1
    · exact block52_pos t ht ht1
    · exact block53_pos t ht ht1
    · exact block54_pos t ht ht1
    · exact block55_pos t ht ht1

end
end DittertRybin.Certificates.SpectralFiveSingleton
