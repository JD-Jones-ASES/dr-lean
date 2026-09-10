import DR.Certificates.FiniteK3Cases.M6N102
import DR.Certificates.FiniteK3Cases.M6N103
import DR.Certificates.FiniteK3Cases.M6N104
import DR.Certificates.FiniteK3Cases.M6N105
import DR.Certificates.FiniteK3Cases.M6N106
import DR.Certificates.FiniteK3Cases.M6N107
import DR.Certificates.FiniteK3Cases.M6N108
import DR.Certificates.FiniteK3Cases.M6N109
import DR.Certificates.FiniteK3Cases.M6N110
import DR.Certificates.FiniteK3Cases.M6N111
import DR.Certificates.FiniteK3Cases.M6N112
import DR.Certificates.FiniteK3Cases.M6N113
import DR.Certificates.FiniteK3Cases.M6N114
import DR.Certificates.FiniteK3Cases.M6N115
import DR.Certificates.FiniteK3Cases.M6N116
import DR.Certificates.FiniteK3Cases.M6N117
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N102To117

theorem exists_valid (n : Nat) (hlo : 102≤n) (hhi : n≤117) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N102.coeff,FiniteK3Cases.C6N102.valid⟩
  · exact ⟨FiniteK3Cases.C6N103.coeff,FiniteK3Cases.C6N103.valid⟩
  · exact ⟨FiniteK3Cases.C6N104.coeff,FiniteK3Cases.C6N104.valid⟩
  · exact ⟨FiniteK3Cases.C6N105.coeff,FiniteK3Cases.C6N105.valid⟩
  · exact ⟨FiniteK3Cases.C6N106.coeff,FiniteK3Cases.C6N106.valid⟩
  · exact ⟨FiniteK3Cases.C6N107.coeff,FiniteK3Cases.C6N107.valid⟩
  · exact ⟨FiniteK3Cases.C6N108.coeff,FiniteK3Cases.C6N108.valid⟩
  · exact ⟨FiniteK3Cases.C6N109.coeff,FiniteK3Cases.C6N109.valid⟩
  · exact ⟨FiniteK3Cases.C6N110.coeff,FiniteK3Cases.C6N110.valid⟩
  · exact ⟨FiniteK3Cases.C6N111.coeff,FiniteK3Cases.C6N111.valid⟩
  · exact ⟨FiniteK3Cases.C6N112.coeff,FiniteK3Cases.C6N112.valid⟩
  · exact ⟨FiniteK3Cases.C6N113.coeff,FiniteK3Cases.C6N113.valid⟩
  · exact ⟨FiniteK3Cases.C6N114.coeff,FiniteK3Cases.C6N114.valid⟩
  · exact ⟨FiniteK3Cases.C6N115.coeff,FiniteK3Cases.C6N115.valid⟩
  · exact ⟨FiniteK3Cases.C6N116.coeff,FiniteK3Cases.C6N116.valid⟩
  · exact ⟨FiniteK3Cases.C6N117.coeff,FiniteK3Cases.C6N117.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N102To117
