import DR.Certificates.FiniteK3Cases.M6N70
import DR.Certificates.FiniteK3Cases.M6N71
import DR.Certificates.FiniteK3Cases.M6N72
import DR.Certificates.FiniteK3Cases.M6N73
import DR.Certificates.FiniteK3Cases.M6N74
import DR.Certificates.FiniteK3Cases.M6N75
import DR.Certificates.FiniteK3Cases.M6N76
import DR.Certificates.FiniteK3Cases.M6N77
import DR.Certificates.FiniteK3Cases.M6N78
import DR.Certificates.FiniteK3Cases.M6N79
import DR.Certificates.FiniteK3Cases.M6N80
import DR.Certificates.FiniteK3Cases.M6N81
import DR.Certificates.FiniteK3Cases.M6N82
import DR.Certificates.FiniteK3Cases.M6N83
import DR.Certificates.FiniteK3Cases.M6N84
import DR.Certificates.FiniteK3Cases.M6N85
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N70To85

theorem exists_valid (n : Nat) (hlo : 70≤n) (hhi : n≤85) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N70.coeff,FiniteK3Cases.C6N70.valid⟩
  · exact ⟨FiniteK3Cases.C6N71.coeff,FiniteK3Cases.C6N71.valid⟩
  · exact ⟨FiniteK3Cases.C6N72.coeff,FiniteK3Cases.C6N72.valid⟩
  · exact ⟨FiniteK3Cases.C6N73.coeff,FiniteK3Cases.C6N73.valid⟩
  · exact ⟨FiniteK3Cases.C6N74.coeff,FiniteK3Cases.C6N74.valid⟩
  · exact ⟨FiniteK3Cases.C6N75.coeff,FiniteK3Cases.C6N75.valid⟩
  · exact ⟨FiniteK3Cases.C6N76.coeff,FiniteK3Cases.C6N76.valid⟩
  · exact ⟨FiniteK3Cases.C6N77.coeff,FiniteK3Cases.C6N77.valid⟩
  · exact ⟨FiniteK3Cases.C6N78.coeff,FiniteK3Cases.C6N78.valid⟩
  · exact ⟨FiniteK3Cases.C6N79.coeff,FiniteK3Cases.C6N79.valid⟩
  · exact ⟨FiniteK3Cases.C6N80.coeff,FiniteK3Cases.C6N80.valid⟩
  · exact ⟨FiniteK3Cases.C6N81.coeff,FiniteK3Cases.C6N81.valid⟩
  · exact ⟨FiniteK3Cases.C6N82.coeff,FiniteK3Cases.C6N82.valid⟩
  · exact ⟨FiniteK3Cases.C6N83.coeff,FiniteK3Cases.C6N83.valid⟩
  · exact ⟨FiniteK3Cases.C6N84.coeff,FiniteK3Cases.C6N84.valid⟩
  · exact ⟨FiniteK3Cases.C6N85.coeff,FiniteK3Cases.C6N85.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N70To85
