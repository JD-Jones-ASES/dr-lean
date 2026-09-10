import DR.Certificates.FiniteK3Cases.M6N198
import DR.Certificates.FiniteK3Cases.M6N199
import DR.Certificates.FiniteK3Cases.M6N200
import DR.Certificates.FiniteK3Cases.M6N201
import DR.Certificates.FiniteK3Cases.M6N202
import DR.Certificates.FiniteK3Cases.M6N203
import DR.Certificates.FiniteK3Cases.M6N204
import DR.Certificates.FiniteK3Cases.M6N205
import DR.Certificates.FiniteK3Cases.M6N206
import DR.Certificates.FiniteK3Cases.M6N207
import DR.Certificates.FiniteK3Cases.M6N208
import DR.Certificates.FiniteK3Cases.M6N209
import DR.Certificates.FiniteK3Cases.M6N210
import DR.Certificates.FiniteK3Cases.M6N211
import DR.Certificates.FiniteK3Cases.M6N212
import DR.Certificates.FiniteK3Cases.M6N213
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N198To213

theorem exists_valid (n : Nat) (hlo : 198≤n) (hhi : n≤213) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N198.coeff,FiniteK3Cases.C6N198.valid⟩
  · exact ⟨FiniteK3Cases.C6N199.coeff,FiniteK3Cases.C6N199.valid⟩
  · exact ⟨FiniteK3Cases.C6N200.coeff,FiniteK3Cases.C6N200.valid⟩
  · exact ⟨FiniteK3Cases.C6N201.coeff,FiniteK3Cases.C6N201.valid⟩
  · exact ⟨FiniteK3Cases.C6N202.coeff,FiniteK3Cases.C6N202.valid⟩
  · exact ⟨FiniteK3Cases.C6N203.coeff,FiniteK3Cases.C6N203.valid⟩
  · exact ⟨FiniteK3Cases.C6N204.coeff,FiniteK3Cases.C6N204.valid⟩
  · exact ⟨FiniteK3Cases.C6N205.coeff,FiniteK3Cases.C6N205.valid⟩
  · exact ⟨FiniteK3Cases.C6N206.coeff,FiniteK3Cases.C6N206.valid⟩
  · exact ⟨FiniteK3Cases.C6N207.coeff,FiniteK3Cases.C6N207.valid⟩
  · exact ⟨FiniteK3Cases.C6N208.coeff,FiniteK3Cases.C6N208.valid⟩
  · exact ⟨FiniteK3Cases.C6N209.coeff,FiniteK3Cases.C6N209.valid⟩
  · exact ⟨FiniteK3Cases.C6N210.coeff,FiniteK3Cases.C6N210.valid⟩
  · exact ⟨FiniteK3Cases.C6N211.coeff,FiniteK3Cases.C6N211.valid⟩
  · exact ⟨FiniteK3Cases.C6N212.coeff,FiniteK3Cases.C6N212.valid⟩
  · exact ⟨FiniteK3Cases.C6N213.coeff,FiniteK3Cases.C6N213.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N198To213
