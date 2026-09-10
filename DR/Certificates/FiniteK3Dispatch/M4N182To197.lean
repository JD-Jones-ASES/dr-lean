import DR.Certificates.FiniteK3Cases.M4N182
import DR.Certificates.FiniteK3Cases.M4N183
import DR.Certificates.FiniteK3Cases.M4N184
import DR.Certificates.FiniteK3Cases.M4N185
import DR.Certificates.FiniteK3Cases.M4N186
import DR.Certificates.FiniteK3Cases.M4N187
import DR.Certificates.FiniteK3Cases.M4N188
import DR.Certificates.FiniteK3Cases.M4N189
import DR.Certificates.FiniteK3Cases.M4N190
import DR.Certificates.FiniteK3Cases.M4N191
import DR.Certificates.FiniteK3Cases.M4N192
import DR.Certificates.FiniteK3Cases.M4N193
import DR.Certificates.FiniteK3Cases.M4N194
import DR.Certificates.FiniteK3Cases.M4N195
import DR.Certificates.FiniteK3Cases.M4N196
import DR.Certificates.FiniteK3Cases.M4N197
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N182To197

theorem exists_valid (n : Nat) (hlo : 182≤n) (hhi : n≤197) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N182.coeff,FiniteK3Cases.C4N182.valid⟩
  · exact ⟨FiniteK3Cases.C4N183.coeff,FiniteK3Cases.C4N183.valid⟩
  · exact ⟨FiniteK3Cases.C4N184.coeff,FiniteK3Cases.C4N184.valid⟩
  · exact ⟨FiniteK3Cases.C4N185.coeff,FiniteK3Cases.C4N185.valid⟩
  · exact ⟨FiniteK3Cases.C4N186.coeff,FiniteK3Cases.C4N186.valid⟩
  · exact ⟨FiniteK3Cases.C4N187.coeff,FiniteK3Cases.C4N187.valid⟩
  · exact ⟨FiniteK3Cases.C4N188.coeff,FiniteK3Cases.C4N188.valid⟩
  · exact ⟨FiniteK3Cases.C4N189.coeff,FiniteK3Cases.C4N189.valid⟩
  · exact ⟨FiniteK3Cases.C4N190.coeff,FiniteK3Cases.C4N190.valid⟩
  · exact ⟨FiniteK3Cases.C4N191.coeff,FiniteK3Cases.C4N191.valid⟩
  · exact ⟨FiniteK3Cases.C4N192.coeff,FiniteK3Cases.C4N192.valid⟩
  · exact ⟨FiniteK3Cases.C4N193.coeff,FiniteK3Cases.C4N193.valid⟩
  · exact ⟨FiniteK3Cases.C4N194.coeff,FiniteK3Cases.C4N194.valid⟩
  · exact ⟨FiniteK3Cases.C4N195.coeff,FiniteK3Cases.C4N195.valid⟩
  · exact ⟨FiniteK3Cases.C4N196.coeff,FiniteK3Cases.C4N196.valid⟩
  · exact ⟨FiniteK3Cases.C4N197.coeff,FiniteK3Cases.C4N197.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N182To197
