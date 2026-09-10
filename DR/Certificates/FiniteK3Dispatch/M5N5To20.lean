import DR.Certificates.FiniteK3Cases.M5N5
import DR.Certificates.FiniteK3Cases.M5N6
import DR.Certificates.FiniteK3Cases.M5N7
import DR.Certificates.FiniteK3Cases.M5N8
import DR.Certificates.FiniteK3Cases.M5N9
import DR.Certificates.FiniteK3Cases.M5N10
import DR.Certificates.FiniteK3Cases.M5N11
import DR.Certificates.FiniteK3Cases.M5N12
import DR.Certificates.FiniteK3Cases.M5N13
import DR.Certificates.FiniteK3Cases.M5N14
import DR.Certificates.FiniteK3Cases.M5N15
import DR.Certificates.FiniteK3Cases.M5N16
import DR.Certificates.FiniteK3Cases.M5N17
import DR.Certificates.FiniteK3Cases.M5N18
import DR.Certificates.FiniteK3Cases.M5N19
import DR.Certificates.FiniteK3Cases.M5N20
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N5To20

theorem exists_valid (n : Nat) (hlo : 5≤n) (hhi : n≤20) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N5.coeff,FiniteK3Cases.C5N5.valid⟩
  · exact ⟨FiniteK3Cases.C5N6.coeff,FiniteK3Cases.C5N6.valid⟩
  · exact ⟨FiniteK3Cases.C5N7.coeff,FiniteK3Cases.C5N7.valid⟩
  · exact ⟨FiniteK3Cases.C5N8.coeff,FiniteK3Cases.C5N8.valid⟩
  · exact ⟨FiniteK3Cases.C5N9.coeff,FiniteK3Cases.C5N9.valid⟩
  · exact ⟨FiniteK3Cases.C5N10.coeff,FiniteK3Cases.C5N10.valid⟩
  · exact ⟨FiniteK3Cases.C5N11.coeff,FiniteK3Cases.C5N11.valid⟩
  · exact ⟨FiniteK3Cases.C5N12.coeff,FiniteK3Cases.C5N12.valid⟩
  · exact ⟨FiniteK3Cases.C5N13.coeff,FiniteK3Cases.C5N13.valid⟩
  · exact ⟨FiniteK3Cases.C5N14.coeff,FiniteK3Cases.C5N14.valid⟩
  · exact ⟨FiniteK3Cases.C5N15.coeff,FiniteK3Cases.C5N15.valid⟩
  · exact ⟨FiniteK3Cases.C5N16.coeff,FiniteK3Cases.C5N16.valid⟩
  · exact ⟨FiniteK3Cases.C5N17.coeff,FiniteK3Cases.C5N17.valid⟩
  · exact ⟨FiniteK3Cases.C5N18.coeff,FiniteK3Cases.C5N18.valid⟩
  · exact ⟨FiniteK3Cases.C5N19.coeff,FiniteK3Cases.C5N19.valid⟩
  · exact ⟨FiniteK3Cases.C5N20.coeff,FiniteK3Cases.C5N20.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N5To20
