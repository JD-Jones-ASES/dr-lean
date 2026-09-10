import DR.Certificates.FiniteK3Cases.M6N182
import DR.Certificates.FiniteK3Cases.M6N183
import DR.Certificates.FiniteK3Cases.M6N184
import DR.Certificates.FiniteK3Cases.M6N185
import DR.Certificates.FiniteK3Cases.M6N186
import DR.Certificates.FiniteK3Cases.M6N187
import DR.Certificates.FiniteK3Cases.M6N188
import DR.Certificates.FiniteK3Cases.M6N189
import DR.Certificates.FiniteK3Cases.M6N190
import DR.Certificates.FiniteK3Cases.M6N191
import DR.Certificates.FiniteK3Cases.M6N192
import DR.Certificates.FiniteK3Cases.M6N193
import DR.Certificates.FiniteK3Cases.M6N194
import DR.Certificates.FiniteK3Cases.M6N195
import DR.Certificates.FiniteK3Cases.M6N196
import DR.Certificates.FiniteK3Cases.M6N197
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N182To197

theorem exists_valid (n : Nat) (hlo : 182≤n) (hhi : n≤197) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N182.coeff,FiniteK3Cases.C6N182.valid⟩
  · exact ⟨FiniteK3Cases.C6N183.coeff,FiniteK3Cases.C6N183.valid⟩
  · exact ⟨FiniteK3Cases.C6N184.coeff,FiniteK3Cases.C6N184.valid⟩
  · exact ⟨FiniteK3Cases.C6N185.coeff,FiniteK3Cases.C6N185.valid⟩
  · exact ⟨FiniteK3Cases.C6N186.coeff,FiniteK3Cases.C6N186.valid⟩
  · exact ⟨FiniteK3Cases.C6N187.coeff,FiniteK3Cases.C6N187.valid⟩
  · exact ⟨FiniteK3Cases.C6N188.coeff,FiniteK3Cases.C6N188.valid⟩
  · exact ⟨FiniteK3Cases.C6N189.coeff,FiniteK3Cases.C6N189.valid⟩
  · exact ⟨FiniteK3Cases.C6N190.coeff,FiniteK3Cases.C6N190.valid⟩
  · exact ⟨FiniteK3Cases.C6N191.coeff,FiniteK3Cases.C6N191.valid⟩
  · exact ⟨FiniteK3Cases.C6N192.coeff,FiniteK3Cases.C6N192.valid⟩
  · exact ⟨FiniteK3Cases.C6N193.coeff,FiniteK3Cases.C6N193.valid⟩
  · exact ⟨FiniteK3Cases.C6N194.coeff,FiniteK3Cases.C6N194.valid⟩
  · exact ⟨FiniteK3Cases.C6N195.coeff,FiniteK3Cases.C6N195.valid⟩
  · exact ⟨FiniteK3Cases.C6N196.coeff,FiniteK3Cases.C6N196.valid⟩
  · exact ⟨FiniteK3Cases.C6N197.coeff,FiniteK3Cases.C6N197.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N182To197
