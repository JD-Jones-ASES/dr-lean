import DR.Certificates.FiniteK3Dispatch.M5N5To20
import DR.Certificates.FiniteK3Dispatch.M5N21To36
import DR.Certificates.FiniteK3Dispatch.M5N37To52
import DR.Certificates.FiniteK3Dispatch.M5N53To68
import DR.Certificates.FiniteK3Dispatch.M5N69To84
import DR.Certificates.FiniteK3Dispatch.M5N85To100
import DR.Certificates.FiniteK3Dispatch.M5N101To116
import DR.Certificates.FiniteK3Dispatch.M5N117To120
import DR.Certificates.FiniteK3EnvelopeSoundness

/-! Generated exact finite-strip assembly; every referenced certificate is required. -/
namespace DittertRybin

theorem uniformMaximizer_orderThree_finite_5 {n : ℕ}
    (hlo : 5 ≤ n) (hhi : n ≤ 120) : UniformMaximizer 5 n 3 := by
  by_cases h20 : n ≤ 20
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N5To20.exists_valid n (by omega) h20
    exact hv.uniformMaximizer (by omega)
  by_cases h36 : n ≤ 36
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N21To36.exists_valid n (by omega) h36
    exact hv.uniformMaximizer (by omega)
  by_cases h52 : n ≤ 52
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N37To52.exists_valid n (by omega) h52
    exact hv.uniformMaximizer (by omega)
  by_cases h68 : n ≤ 68
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N53To68.exists_valid n (by omega) h68
    exact hv.uniformMaximizer (by omega)
  by_cases h84 : n ≤ 84
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N69To84.exists_valid n (by omega) h84
    exact hv.uniformMaximizer (by omega)
  by_cases h100 : n ≤ 100
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N85To100.exists_valid n (by omega) h100
    exact hv.uniformMaximizer (by omega)
  by_cases h116 : n ≤ 116
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N101To116.exists_valid n (by omega) h116
    exact hv.uniformMaximizer (by omega)
  obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C5N117To120.exists_valid n (by omega) hhi
  exact hv.uniformMaximizer (by omega)

end DittertRybin
