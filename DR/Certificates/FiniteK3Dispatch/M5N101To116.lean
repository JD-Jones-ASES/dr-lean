import DR.Certificates.FiniteK3Cases.M5N101
import DR.Certificates.FiniteK3Cases.M5N102
import DR.Certificates.FiniteK3Cases.M5N103
import DR.Certificates.FiniteK3Cases.M5N104
import DR.Certificates.FiniteK3Cases.M5N105
import DR.Certificates.FiniteK3Cases.M5N106
import DR.Certificates.FiniteK3Cases.M5N107
import DR.Certificates.FiniteK3Cases.M5N108
import DR.Certificates.FiniteK3Cases.M5N109
import DR.Certificates.FiniteK3Cases.M5N110
import DR.Certificates.FiniteK3Cases.M5N111
import DR.Certificates.FiniteK3Cases.M5N112
import DR.Certificates.FiniteK3Cases.M5N113
import DR.Certificates.FiniteK3Cases.M5N114
import DR.Certificates.FiniteK3Cases.M5N115
import DR.Certificates.FiniteK3Cases.M5N116
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N101To116

theorem exists_valid (n : Nat) (hlo : 101≤n) (hhi : n≤116) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N101.coeff,FiniteK3Cases.C5N101.valid⟩
  · exact ⟨FiniteK3Cases.C5N102.coeff,FiniteK3Cases.C5N102.valid⟩
  · exact ⟨FiniteK3Cases.C5N103.coeff,FiniteK3Cases.C5N103.valid⟩
  · exact ⟨FiniteK3Cases.C5N104.coeff,FiniteK3Cases.C5N104.valid⟩
  · exact ⟨FiniteK3Cases.C5N105.coeff,FiniteK3Cases.C5N105.valid⟩
  · exact ⟨FiniteK3Cases.C5N106.coeff,FiniteK3Cases.C5N106.valid⟩
  · exact ⟨FiniteK3Cases.C5N107.coeff,FiniteK3Cases.C5N107.valid⟩
  · exact ⟨FiniteK3Cases.C5N108.coeff,FiniteK3Cases.C5N108.valid⟩
  · exact ⟨FiniteK3Cases.C5N109.coeff,FiniteK3Cases.C5N109.valid⟩
  · exact ⟨FiniteK3Cases.C5N110.coeff,FiniteK3Cases.C5N110.valid⟩
  · exact ⟨FiniteK3Cases.C5N111.coeff,FiniteK3Cases.C5N111.valid⟩
  · exact ⟨FiniteK3Cases.C5N112.coeff,FiniteK3Cases.C5N112.valid⟩
  · exact ⟨FiniteK3Cases.C5N113.coeff,FiniteK3Cases.C5N113.valid⟩
  · exact ⟨FiniteK3Cases.C5N114.coeff,FiniteK3Cases.C5N114.valid⟩
  · exact ⟨FiniteK3Cases.C5N115.coeff,FiniteK3Cases.C5N115.valid⟩
  · exact ⟨FiniteK3Cases.C5N116.coeff,FiniteK3Cases.C5N116.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N101To116
