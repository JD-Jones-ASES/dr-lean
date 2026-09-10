import DR.Certificates.FiniteK3Cases.M4N102
import DR.Certificates.FiniteK3Cases.M4N103
import DR.Certificates.FiniteK3Cases.M4N104
import DR.Certificates.FiniteK3Cases.M4N105
import DR.Certificates.FiniteK3Cases.M4N106
import DR.Certificates.FiniteK3Cases.M4N107
import DR.Certificates.FiniteK3Cases.M4N108
import DR.Certificates.FiniteK3Cases.M4N109
import DR.Certificates.FiniteK3Cases.M4N110
import DR.Certificates.FiniteK3Cases.M4N111
import DR.Certificates.FiniteK3Cases.M4N112
import DR.Certificates.FiniteK3Cases.M4N113
import DR.Certificates.FiniteK3Cases.M4N114
import DR.Certificates.FiniteK3Cases.M4N115
import DR.Certificates.FiniteK3Cases.M4N116
import DR.Certificates.FiniteK3Cases.M4N117
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N102To117

theorem exists_valid (n : Nat) (hlo : 102≤n) (hhi : n≤117) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N102.coeff,FiniteK3Cases.C4N102.valid⟩
  · exact ⟨FiniteK3Cases.C4N103.coeff,FiniteK3Cases.C4N103.valid⟩
  · exact ⟨FiniteK3Cases.C4N104.coeff,FiniteK3Cases.C4N104.valid⟩
  · exact ⟨FiniteK3Cases.C4N105.coeff,FiniteK3Cases.C4N105.valid⟩
  · exact ⟨FiniteK3Cases.C4N106.coeff,FiniteK3Cases.C4N106.valid⟩
  · exact ⟨FiniteK3Cases.C4N107.coeff,FiniteK3Cases.C4N107.valid⟩
  · exact ⟨FiniteK3Cases.C4N108.coeff,FiniteK3Cases.C4N108.valid⟩
  · exact ⟨FiniteK3Cases.C4N109.coeff,FiniteK3Cases.C4N109.valid⟩
  · exact ⟨FiniteK3Cases.C4N110.coeff,FiniteK3Cases.C4N110.valid⟩
  · exact ⟨FiniteK3Cases.C4N111.coeff,FiniteK3Cases.C4N111.valid⟩
  · exact ⟨FiniteK3Cases.C4N112.coeff,FiniteK3Cases.C4N112.valid⟩
  · exact ⟨FiniteK3Cases.C4N113.coeff,FiniteK3Cases.C4N113.valid⟩
  · exact ⟨FiniteK3Cases.C4N114.coeff,FiniteK3Cases.C4N114.valid⟩
  · exact ⟨FiniteK3Cases.C4N115.coeff,FiniteK3Cases.C4N115.valid⟩
  · exact ⟨FiniteK3Cases.C4N116.coeff,FiniteK3Cases.C4N116.valid⟩
  · exact ⟨FiniteK3Cases.C4N117.coeff,FiniteK3Cases.C4N117.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N102To117
