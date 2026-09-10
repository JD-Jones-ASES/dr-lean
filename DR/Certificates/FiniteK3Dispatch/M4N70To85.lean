import DR.Certificates.FiniteK3Cases.M4N70
import DR.Certificates.FiniteK3Cases.M4N71
import DR.Certificates.FiniteK3Cases.M4N72
import DR.Certificates.FiniteK3Cases.M4N73
import DR.Certificates.FiniteK3Cases.M4N74
import DR.Certificates.FiniteK3Cases.M4N75
import DR.Certificates.FiniteK3Cases.M4N76
import DR.Certificates.FiniteK3Cases.M4N77
import DR.Certificates.FiniteK3Cases.M4N78
import DR.Certificates.FiniteK3Cases.M4N79
import DR.Certificates.FiniteK3Cases.M4N80
import DR.Certificates.FiniteK3Cases.M4N81
import DR.Certificates.FiniteK3Cases.M4N82
import DR.Certificates.FiniteK3Cases.M4N83
import DR.Certificates.FiniteK3Cases.M4N84
import DR.Certificates.FiniteK3Cases.M4N85
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N70To85

theorem exists_valid (n : Nat) (hlo : 70≤n) (hhi : n≤85) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N70.coeff,FiniteK3Cases.C4N70.valid⟩
  · exact ⟨FiniteK3Cases.C4N71.coeff,FiniteK3Cases.C4N71.valid⟩
  · exact ⟨FiniteK3Cases.C4N72.coeff,FiniteK3Cases.C4N72.valid⟩
  · exact ⟨FiniteK3Cases.C4N73.coeff,FiniteK3Cases.C4N73.valid⟩
  · exact ⟨FiniteK3Cases.C4N74.coeff,FiniteK3Cases.C4N74.valid⟩
  · exact ⟨FiniteK3Cases.C4N75.coeff,FiniteK3Cases.C4N75.valid⟩
  · exact ⟨FiniteK3Cases.C4N76.coeff,FiniteK3Cases.C4N76.valid⟩
  · exact ⟨FiniteK3Cases.C4N77.coeff,FiniteK3Cases.C4N77.valid⟩
  · exact ⟨FiniteK3Cases.C4N78.coeff,FiniteK3Cases.C4N78.valid⟩
  · exact ⟨FiniteK3Cases.C4N79.coeff,FiniteK3Cases.C4N79.valid⟩
  · exact ⟨FiniteK3Cases.C4N80.coeff,FiniteK3Cases.C4N80.valid⟩
  · exact ⟨FiniteK3Cases.C4N81.coeff,FiniteK3Cases.C4N81.valid⟩
  · exact ⟨FiniteK3Cases.C4N82.coeff,FiniteK3Cases.C4N82.valid⟩
  · exact ⟨FiniteK3Cases.C4N83.coeff,FiniteK3Cases.C4N83.valid⟩
  · exact ⟨FiniteK3Cases.C4N84.coeff,FiniteK3Cases.C4N84.valid⟩
  · exact ⟨FiniteK3Cases.C4N85.coeff,FiniteK3Cases.C4N85.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N70To85
