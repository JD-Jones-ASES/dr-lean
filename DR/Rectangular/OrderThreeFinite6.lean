import DR.Certificates.FiniteK3Dispatch.M6N6To21
import DR.Certificates.FiniteK3Dispatch.M6N22To37
import DR.Certificates.FiniteK3Dispatch.M6N38To53
import DR.Certificates.FiniteK3Dispatch.M6N54To69
import DR.Certificates.FiniteK3Dispatch.M6N70To85
import DR.Certificates.FiniteK3Dispatch.M6N86To101
import DR.Certificates.FiniteK3Dispatch.M6N102To117
import DR.Certificates.FiniteK3Dispatch.M6N118To133
import DR.Certificates.FiniteK3Dispatch.M6N134To149
import DR.Certificates.FiniteK3Dispatch.M6N150To165
import DR.Certificates.FiniteK3Dispatch.M6N166To181
import DR.Certificates.FiniteK3Dispatch.M6N182To197
import DR.Certificates.FiniteK3Dispatch.M6N198To213
import DR.Certificates.FiniteK3Dispatch.M6N214To229
import DR.Certificates.FiniteK3Dispatch.M6N230To237
import DR.Certificates.FiniteK3EnvelopeSoundness

/-! Generated exact finite-strip assembly; every referenced certificate is required. -/
namespace DittertRybin

theorem uniformMaximizer_orderThree_finite_6 {n : ℕ}
    (hlo : 6 ≤ n) (hhi : n ≤ 237) : UniformMaximizer 6 n 3 := by
  by_cases h21 : n ≤ 21
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N6To21.exists_valid n (by omega) h21
    exact hv.uniformMaximizer (by omega)
  by_cases h37 : n ≤ 37
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N22To37.exists_valid n (by omega) h37
    exact hv.uniformMaximizer (by omega)
  by_cases h53 : n ≤ 53
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N38To53.exists_valid n (by omega) h53
    exact hv.uniformMaximizer (by omega)
  by_cases h69 : n ≤ 69
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N54To69.exists_valid n (by omega) h69
    exact hv.uniformMaximizer (by omega)
  by_cases h85 : n ≤ 85
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N70To85.exists_valid n (by omega) h85
    exact hv.uniformMaximizer (by omega)
  by_cases h101 : n ≤ 101
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N86To101.exists_valid n (by omega) h101
    exact hv.uniformMaximizer (by omega)
  by_cases h117 : n ≤ 117
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N102To117.exists_valid n (by omega) h117
    exact hv.uniformMaximizer (by omega)
  by_cases h133 : n ≤ 133
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N118To133.exists_valid n (by omega) h133
    exact hv.uniformMaximizer (by omega)
  by_cases h149 : n ≤ 149
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N134To149.exists_valid n (by omega) h149
    exact hv.uniformMaximizer (by omega)
  by_cases h165 : n ≤ 165
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N150To165.exists_valid n (by omega) h165
    exact hv.uniformMaximizer (by omega)
  by_cases h181 : n ≤ 181
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N166To181.exists_valid n (by omega) h181
    exact hv.uniformMaximizer (by omega)
  by_cases h197 : n ≤ 197
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N182To197.exists_valid n (by omega) h197
    exact hv.uniformMaximizer (by omega)
  by_cases h213 : n ≤ 213
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N198To213.exists_valid n (by omega) h213
    exact hv.uniformMaximizer (by omega)
  by_cases h229 : n ≤ 229
  · obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N214To229.exists_valid n (by omega) h229
    exact hv.uniformMaximizer (by omega)
  obtain ⟨coeff,hv⟩ := Certificates.FiniteK3Dispatch.C6N230To237.exists_valid n (by omega) hhi
  exact hv.uniformMaximizer (by omega)

end DittertRybin
