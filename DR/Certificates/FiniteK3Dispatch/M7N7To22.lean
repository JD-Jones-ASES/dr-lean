import DR.Certificates.FiniteK3Cases.M7N7
import DR.Certificates.FiniteK3Cases.M7N8
import DR.Certificates.FiniteK3Cases.M7N9
import DR.Certificates.FiniteK3Cases.M7N10
import DR.Certificates.FiniteK3Cases.M7N11
import DR.Certificates.FiniteK3Cases.M7N12
import DR.Certificates.FiniteK3Cases.M7N13
import DR.Certificates.FiniteK3Cases.M7N14
import DR.Certificates.FiniteK3Cases.M7N15
import DR.Certificates.FiniteK3Cases.M7N16
import DR.Certificates.FiniteK3Cases.M7N17
import DR.Certificates.FiniteK3Cases.M7N18
import DR.Certificates.FiniteK3Cases.M7N19
import DR.Certificates.FiniteK3Cases.M7N20
import DR.Certificates.FiniteK3Cases.M7N21
import DR.Certificates.FiniteK3Cases.M7N22
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C7N7To22

theorem exists_valid (n : Nat) (hlo : 7≤n) (hhi : n≤22) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 7 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C7N7.coeff,FiniteK3Cases.C7N7.valid⟩
  · exact ⟨FiniteK3Cases.C7N8.coeff,FiniteK3Cases.C7N8.valid⟩
  · exact ⟨FiniteK3Cases.C7N9.coeff,FiniteK3Cases.C7N9.valid⟩
  · exact ⟨FiniteK3Cases.C7N10.coeff,FiniteK3Cases.C7N10.valid⟩
  · exact ⟨FiniteK3Cases.C7N11.coeff,FiniteK3Cases.C7N11.valid⟩
  · exact ⟨FiniteK3Cases.C7N12.coeff,FiniteK3Cases.C7N12.valid⟩
  · exact ⟨FiniteK3Cases.C7N13.coeff,FiniteK3Cases.C7N13.valid⟩
  · exact ⟨FiniteK3Cases.C7N14.coeff,FiniteK3Cases.C7N14.valid⟩
  · exact ⟨FiniteK3Cases.C7N15.coeff,FiniteK3Cases.C7N15.valid⟩
  · exact ⟨FiniteK3Cases.C7N16.coeff,FiniteK3Cases.C7N16.valid⟩
  · exact ⟨FiniteK3Cases.C7N17.coeff,FiniteK3Cases.C7N17.valid⟩
  · exact ⟨FiniteK3Cases.C7N18.coeff,FiniteK3Cases.C7N18.valid⟩
  · exact ⟨FiniteK3Cases.C7N19.coeff,FiniteK3Cases.C7N19.valid⟩
  · exact ⟨FiniteK3Cases.C7N20.coeff,FiniteK3Cases.C7N20.valid⟩
  · exact ⟨FiniteK3Cases.C7N21.coeff,FiniteK3Cases.C7N21.valid⟩
  · exact ⟨FiniteK3Cases.C7N22.coeff,FiniteK3Cases.C7N22.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C7N7To22
