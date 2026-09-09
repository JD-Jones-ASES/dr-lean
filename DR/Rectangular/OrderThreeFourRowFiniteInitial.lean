import DR.Certificates.FiniteK3EnvelopeSoundness
import DR.Certificates.FiniteK3Dispatch.M4N6To21

/-! The first fully replayed contiguous part of the finite K3 envelope.
Both endpoints are included; the full 1330-case dispatcher is separate. -/

namespace DittertRybin

theorem uniformMaximizer_orderThree_four_rows_six_to_twentyOne {n : ℕ}
    (hlo : 6 ≤ n) (hhi : n ≤ 21) : UniformMaximizer 4 n 3 := by
  obtain ⟨coeff, h⟩ := Certificates.FiniteK3Dispatch.C4N6To21.exists_valid n hlo hhi
  exact h.uniformMaximizer (by omega)

end DittertRybin
