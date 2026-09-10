import DR.Certificates.FiniteK3Cases.M4N310
import DR.Certificates.FiniteK3Cases.M4N311
import DR.Certificates.FiniteK3Cases.M4N312
import DR.Certificates.FiniteK3Cases.M4N313
import DR.Certificates.FiniteK3Cases.M4N314
import DR.Certificates.FiniteK3Cases.M4N315
import DR.Certificates.FiniteK3Cases.M4N316
import DR.Certificates.FiniteK3Cases.M4N317
import DR.Certificates.FiniteK3Cases.M4N318
import DR.Certificates.FiniteK3Cases.M4N319
import DR.Certificates.FiniteK3Cases.M4N320
import DR.Certificates.FiniteK3Cases.M4N321
import DR.Certificates.FiniteK3Cases.M4N322
import DR.Certificates.FiniteK3Cases.M4N323
import DR.Certificates.FiniteK3Cases.M4N324
import DR.Certificates.FiniteK3Cases.M4N325
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N310To325

theorem exists_valid (n : Nat) (hlo : 310≤n) (hhi : n≤325) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N310.coeff,FiniteK3Cases.C4N310.valid⟩
  · exact ⟨FiniteK3Cases.C4N311.coeff,FiniteK3Cases.C4N311.valid⟩
  · exact ⟨FiniteK3Cases.C4N312.coeff,FiniteK3Cases.C4N312.valid⟩
  · exact ⟨FiniteK3Cases.C4N313.coeff,FiniteK3Cases.C4N313.valid⟩
  · exact ⟨FiniteK3Cases.C4N314.coeff,FiniteK3Cases.C4N314.valid⟩
  · exact ⟨FiniteK3Cases.C4N315.coeff,FiniteK3Cases.C4N315.valid⟩
  · exact ⟨FiniteK3Cases.C4N316.coeff,FiniteK3Cases.C4N316.valid⟩
  · exact ⟨FiniteK3Cases.C4N317.coeff,FiniteK3Cases.C4N317.valid⟩
  · exact ⟨FiniteK3Cases.C4N318.coeff,FiniteK3Cases.C4N318.valid⟩
  · exact ⟨FiniteK3Cases.C4N319.coeff,FiniteK3Cases.C4N319.valid⟩
  · exact ⟨FiniteK3Cases.C4N320.coeff,FiniteK3Cases.C4N320.valid⟩
  · exact ⟨FiniteK3Cases.C4N321.coeff,FiniteK3Cases.C4N321.valid⟩
  · exact ⟨FiniteK3Cases.C4N322.coeff,FiniteK3Cases.C4N322.valid⟩
  · exact ⟨FiniteK3Cases.C4N323.coeff,FiniteK3Cases.C4N323.valid⟩
  · exact ⟨FiniteK3Cases.C4N324.coeff,FiniteK3Cases.C4N324.valid⟩
  · exact ⟨FiniteK3Cases.C4N325.coeff,FiniteK3Cases.C4N325.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N310To325
