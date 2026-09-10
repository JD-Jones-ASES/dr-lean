import DR.Certificates.FiniteK3Dispatch.M9N9To11
import DR.Certificates.FiniteK3EnvelopeSoundness

/-! Generated exact finite-strip assembly; every referenced certificate is required. -/
namespace DittertRybin

theorem uniformMaximizer_orderThree_finite_9 {n : ℕ}
    (hlo : 9 ≤ n) (hhi : n ≤ 11) : UniformMaximizer 9 n 3 := by
  obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C9N9To11.exists_valid n (by omega) hhi
  exact hv.uniformMaximizer (by omega)

end DittertRybin
