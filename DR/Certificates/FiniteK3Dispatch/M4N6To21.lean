import DR.Certificates.FiniteK3Cases.M4N6
import DR.Certificates.FiniteK3Cases.M4N7
import DR.Certificates.FiniteK3Cases.M4N8
import DR.Certificates.FiniteK3Cases.M4N9
import DR.Certificates.FiniteK3Cases.M4N10
import DR.Certificates.FiniteK3Cases.M4N11
import DR.Certificates.FiniteK3Cases.M4N12
import DR.Certificates.FiniteK3Cases.M4N13
import DR.Certificates.FiniteK3Cases.M4N14
import DR.Certificates.FiniteK3Cases.M4N15
import DR.Certificates.FiniteK3Cases.M4N16
import DR.Certificates.FiniteK3Cases.M4N17
import DR.Certificates.FiniteK3Cases.M4N18
import DR.Certificates.FiniteK3Cases.M4N19
import DR.Certificates.FiniteK3Cases.M4N20
import DR.Certificates.FiniteK3Cases.M4N21
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N6To21

theorem exists_valid (n : Nat) (hlo : 6≤n) (hhi : n≤21) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N6.coeff,FiniteK3Cases.C4N6.valid⟩
  · exact ⟨FiniteK3Cases.C4N7.coeff,FiniteK3Cases.C4N7.valid⟩
  · exact ⟨FiniteK3Cases.C4N8.coeff,FiniteK3Cases.C4N8.valid⟩
  · exact ⟨FiniteK3Cases.C4N9.coeff,FiniteK3Cases.C4N9.valid⟩
  · exact ⟨FiniteK3Cases.C4N10.coeff,FiniteK3Cases.C4N10.valid⟩
  · exact ⟨FiniteK3Cases.C4N11.coeff,FiniteK3Cases.C4N11.valid⟩
  · exact ⟨FiniteK3Cases.C4N12.coeff,FiniteK3Cases.C4N12.valid⟩
  · exact ⟨FiniteK3Cases.C4N13.coeff,FiniteK3Cases.C4N13.valid⟩
  · exact ⟨FiniteK3Cases.C4N14.coeff,FiniteK3Cases.C4N14.valid⟩
  · exact ⟨FiniteK3Cases.C4N15.coeff,FiniteK3Cases.C4N15.valid⟩
  · exact ⟨FiniteK3Cases.C4N16.coeff,FiniteK3Cases.C4N16.valid⟩
  · exact ⟨FiniteK3Cases.C4N17.coeff,FiniteK3Cases.C4N17.valid⟩
  · exact ⟨FiniteK3Cases.C4N18.coeff,FiniteK3Cases.C4N18.valid⟩
  · exact ⟨FiniteK3Cases.C4N19.coeff,FiniteK3Cases.C4N19.valid⟩
  · exact ⟨FiniteK3Cases.C4N20.coeff,FiniteK3Cases.C4N20.valid⟩
  · exact ⟨FiniteK3Cases.C4N21.coeff,FiniteK3Cases.C4N21.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N6To21
