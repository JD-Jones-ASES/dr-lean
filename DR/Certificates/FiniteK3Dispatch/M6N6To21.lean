import DR.Certificates.FiniteK3Cases.M6N6
import DR.Certificates.FiniteK3Cases.M6N7
import DR.Certificates.FiniteK3Cases.M6N8
import DR.Certificates.FiniteK3Cases.M6N9
import DR.Certificates.FiniteK3Cases.M6N10
import DR.Certificates.FiniteK3Cases.M6N11
import DR.Certificates.FiniteK3Cases.M6N12
import DR.Certificates.FiniteK3Cases.M6N13
import DR.Certificates.FiniteK3Cases.M6N14
import DR.Certificates.FiniteK3Cases.M6N15
import DR.Certificates.FiniteK3Cases.M6N16
import DR.Certificates.FiniteK3Cases.M6N17
import DR.Certificates.FiniteK3Cases.M6N18
import DR.Certificates.FiniteK3Cases.M6N19
import DR.Certificates.FiniteK3Cases.M6N20
import DR.Certificates.FiniteK3Cases.M6N21
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N6To21

theorem exists_valid (n : Nat) (hlo : 6≤n) (hhi : n≤21) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N6.coeff,FiniteK3Cases.C6N6.valid⟩
  · exact ⟨FiniteK3Cases.C6N7.coeff,FiniteK3Cases.C6N7.valid⟩
  · exact ⟨FiniteK3Cases.C6N8.coeff,FiniteK3Cases.C6N8.valid⟩
  · exact ⟨FiniteK3Cases.C6N9.coeff,FiniteK3Cases.C6N9.valid⟩
  · exact ⟨FiniteK3Cases.C6N10.coeff,FiniteK3Cases.C6N10.valid⟩
  · exact ⟨FiniteK3Cases.C6N11.coeff,FiniteK3Cases.C6N11.valid⟩
  · exact ⟨FiniteK3Cases.C6N12.coeff,FiniteK3Cases.C6N12.valid⟩
  · exact ⟨FiniteK3Cases.C6N13.coeff,FiniteK3Cases.C6N13.valid⟩
  · exact ⟨FiniteK3Cases.C6N14.coeff,FiniteK3Cases.C6N14.valid⟩
  · exact ⟨FiniteK3Cases.C6N15.coeff,FiniteK3Cases.C6N15.valid⟩
  · exact ⟨FiniteK3Cases.C6N16.coeff,FiniteK3Cases.C6N16.valid⟩
  · exact ⟨FiniteK3Cases.C6N17.coeff,FiniteK3Cases.C6N17.valid⟩
  · exact ⟨FiniteK3Cases.C6N18.coeff,FiniteK3Cases.C6N18.valid⟩
  · exact ⟨FiniteK3Cases.C6N19.coeff,FiniteK3Cases.C6N19.valid⟩
  · exact ⟨FiniteK3Cases.C6N20.coeff,FiniteK3Cases.C6N20.valid⟩
  · exact ⟨FiniteK3Cases.C6N21.coeff,FiniteK3Cases.C6N21.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N6To21
