import DR.Certificates.FiniteK3Cases.M5N69
import DR.Certificates.FiniteK3Cases.M5N70
import DR.Certificates.FiniteK3Cases.M5N71
import DR.Certificates.FiniteK3Cases.M5N72
import DR.Certificates.FiniteK3Cases.M5N73
import DR.Certificates.FiniteK3Cases.M5N74
import DR.Certificates.FiniteK3Cases.M5N75
import DR.Certificates.FiniteK3Cases.M5N76
import DR.Certificates.FiniteK3Cases.M5N77
import DR.Certificates.FiniteK3Cases.M5N78
import DR.Certificates.FiniteK3Cases.M5N79
import DR.Certificates.FiniteK3Cases.M5N80
import DR.Certificates.FiniteK3Cases.M5N81
import DR.Certificates.FiniteK3Cases.M5N82
import DR.Certificates.FiniteK3Cases.M5N83
import DR.Certificates.FiniteK3Cases.M5N84
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N69To84

theorem exists_valid (n : Nat) (hlo : 69≤n) (hhi : n≤84) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N69.coeff,FiniteK3Cases.C5N69.valid⟩
  · exact ⟨FiniteK3Cases.C5N70.coeff,FiniteK3Cases.C5N70.valid⟩
  · exact ⟨FiniteK3Cases.C5N71.coeff,FiniteK3Cases.C5N71.valid⟩
  · exact ⟨FiniteK3Cases.C5N72.coeff,FiniteK3Cases.C5N72.valid⟩
  · exact ⟨FiniteK3Cases.C5N73.coeff,FiniteK3Cases.C5N73.valid⟩
  · exact ⟨FiniteK3Cases.C5N74.coeff,FiniteK3Cases.C5N74.valid⟩
  · exact ⟨FiniteK3Cases.C5N75.coeff,FiniteK3Cases.C5N75.valid⟩
  · exact ⟨FiniteK3Cases.C5N76.coeff,FiniteK3Cases.C5N76.valid⟩
  · exact ⟨FiniteK3Cases.C5N77.coeff,FiniteK3Cases.C5N77.valid⟩
  · exact ⟨FiniteK3Cases.C5N78.coeff,FiniteK3Cases.C5N78.valid⟩
  · exact ⟨FiniteK3Cases.C5N79.coeff,FiniteK3Cases.C5N79.valid⟩
  · exact ⟨FiniteK3Cases.C5N80.coeff,FiniteK3Cases.C5N80.valid⟩
  · exact ⟨FiniteK3Cases.C5N81.coeff,FiniteK3Cases.C5N81.valid⟩
  · exact ⟨FiniteK3Cases.C5N82.coeff,FiniteK3Cases.C5N82.valid⟩
  · exact ⟨FiniteK3Cases.C5N83.coeff,FiniteK3Cases.C5N83.valid⟩
  · exact ⟨FiniteK3Cases.C5N84.coeff,FiniteK3Cases.C5N84.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N69To84
