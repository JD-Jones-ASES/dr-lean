import DR.Certificates.FiniteK3Cases.M8N8
import DR.Certificates.FiniteK3Cases.M8N9
import DR.Certificates.FiniteK3Cases.M8N10
import DR.Certificates.FiniteK3Cases.M8N11
import DR.Certificates.FiniteK3Cases.M8N12
import DR.Certificates.FiniteK3Cases.M8N13
import DR.Certificates.FiniteK3Cases.M8N14
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C8N8To14

theorem exists_valid (n : Nat) (hlo : 8≤n) (hhi : n≤14) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 8 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C8N8.coeff,FiniteK3Cases.C8N8.valid⟩
  · exact ⟨FiniteK3Cases.C8N9.coeff,FiniteK3Cases.C8N9.valid⟩
  · exact ⟨FiniteK3Cases.C8N10.coeff,FiniteK3Cases.C8N10.valid⟩
  · exact ⟨FiniteK3Cases.C8N11.coeff,FiniteK3Cases.C8N11.valid⟩
  · exact ⟨FiniteK3Cases.C8N12.coeff,FiniteK3Cases.C8N12.valid⟩
  · exact ⟨FiniteK3Cases.C8N13.coeff,FiniteK3Cases.C8N13.valid⟩
  · exact ⟨FiniteK3Cases.C8N14.coeff,FiniteK3Cases.C8N14.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C8N8To14
