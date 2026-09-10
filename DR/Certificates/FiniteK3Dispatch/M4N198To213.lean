import DR.Certificates.FiniteK3Cases.M4N198
import DR.Certificates.FiniteK3Cases.M4N199
import DR.Certificates.FiniteK3Cases.M4N200
import DR.Certificates.FiniteK3Cases.M4N201
import DR.Certificates.FiniteK3Cases.M4N202
import DR.Certificates.FiniteK3Cases.M4N203
import DR.Certificates.FiniteK3Cases.M4N204
import DR.Certificates.FiniteK3Cases.M4N205
import DR.Certificates.FiniteK3Cases.M4N206
import DR.Certificates.FiniteK3Cases.M4N207
import DR.Certificates.FiniteK3Cases.M4N208
import DR.Certificates.FiniteK3Cases.M4N209
import DR.Certificates.FiniteK3Cases.M4N210
import DR.Certificates.FiniteK3Cases.M4N211
import DR.Certificates.FiniteK3Cases.M4N212
import DR.Certificates.FiniteK3Cases.M4N213
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N198To213

theorem exists_valid (n : Nat) (hlo : 198≤n) (hhi : n≤213) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N198.coeff,FiniteK3Cases.C4N198.valid⟩
  · exact ⟨FiniteK3Cases.C4N199.coeff,FiniteK3Cases.C4N199.valid⟩
  · exact ⟨FiniteK3Cases.C4N200.coeff,FiniteK3Cases.C4N200.valid⟩
  · exact ⟨FiniteK3Cases.C4N201.coeff,FiniteK3Cases.C4N201.valid⟩
  · exact ⟨FiniteK3Cases.C4N202.coeff,FiniteK3Cases.C4N202.valid⟩
  · exact ⟨FiniteK3Cases.C4N203.coeff,FiniteK3Cases.C4N203.valid⟩
  · exact ⟨FiniteK3Cases.C4N204.coeff,FiniteK3Cases.C4N204.valid⟩
  · exact ⟨FiniteK3Cases.C4N205.coeff,FiniteK3Cases.C4N205.valid⟩
  · exact ⟨FiniteK3Cases.C4N206.coeff,FiniteK3Cases.C4N206.valid⟩
  · exact ⟨FiniteK3Cases.C4N207.coeff,FiniteK3Cases.C4N207.valid⟩
  · exact ⟨FiniteK3Cases.C4N208.coeff,FiniteK3Cases.C4N208.valid⟩
  · exact ⟨FiniteK3Cases.C4N209.coeff,FiniteK3Cases.C4N209.valid⟩
  · exact ⟨FiniteK3Cases.C4N210.coeff,FiniteK3Cases.C4N210.valid⟩
  · exact ⟨FiniteK3Cases.C4N211.coeff,FiniteK3Cases.C4N211.valid⟩
  · exact ⟨FiniteK3Cases.C4N212.coeff,FiniteK3Cases.C4N212.valid⟩
  · exact ⟨FiniteK3Cases.C4N213.coeff,FiniteK3Cases.C4N213.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N198To213
