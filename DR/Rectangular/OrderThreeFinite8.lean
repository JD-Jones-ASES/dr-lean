import DR.Certificates.FiniteK3Dispatch.M8N8To14
import DR.Certificates.FiniteK3EnvelopeSoundness

/-! Generated exact finite-strip assembly; every referenced certificate is required. -/
namespace DittertRybin

theorem uniformMaximizer_orderThree_finite_8 {n : ℕ}
    (hlo : 8 ≤ n) (hhi : n ≤ 14) : UniformMaximizer 8 n 3 := by
  obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C8N8To14.exists_valid n (by omega) hhi
  exact hv.uniformMaximizer (by omega)

end DittertRybin
