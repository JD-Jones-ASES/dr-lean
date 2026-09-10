import DR.Certificates.FiniteK3Dispatch.M7N7To22
import DR.Certificates.FiniteK3Dispatch.M7N23To24
import DR.Certificates.FiniteK3EnvelopeSoundness

/-! Generated exact finite-strip assembly; every referenced certificate is required. -/
namespace DittertRybin

theorem uniformMaximizer_orderThree_finite_7 {n : ℕ}
    (hlo : 7 ≤ n) (hhi : n ≤ 24) : UniformMaximizer 7 n 3 := by
  by_cases h22 : n ≤ 22
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C7N7To22.exists_valid n (by omega) h22
    exact hv.uniformMaximizer (by omega)
  obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C7N23To24.exists_valid n (by omega) hhi
  exact hv.uniformMaximizer (by omega)

end DittertRybin
