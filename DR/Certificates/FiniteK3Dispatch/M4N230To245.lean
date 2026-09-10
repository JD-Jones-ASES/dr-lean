import DR.Certificates.FiniteK3Cases.M4N230
import DR.Certificates.FiniteK3Cases.M4N231
import DR.Certificates.FiniteK3Cases.M4N232
import DR.Certificates.FiniteK3Cases.M4N233
import DR.Certificates.FiniteK3Cases.M4N234
import DR.Certificates.FiniteK3Cases.M4N235
import DR.Certificates.FiniteK3Cases.M4N236
import DR.Certificates.FiniteK3Cases.M4N237
import DR.Certificates.FiniteK3Cases.M4N238
import DR.Certificates.FiniteK3Cases.M4N239
import DR.Certificates.FiniteK3Cases.M4N240
import DR.Certificates.FiniteK3Cases.M4N241
import DR.Certificates.FiniteK3Cases.M4N242
import DR.Certificates.FiniteK3Cases.M4N243
import DR.Certificates.FiniteK3Cases.M4N244
import DR.Certificates.FiniteK3Cases.M4N245
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N230To245

theorem exists_valid (n : Nat) (hlo : 230≤n) (hhi : n≤245) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N230.coeff,FiniteK3Cases.C4N230.valid⟩
  · exact ⟨FiniteK3Cases.C4N231.coeff,FiniteK3Cases.C4N231.valid⟩
  · exact ⟨FiniteK3Cases.C4N232.coeff,FiniteK3Cases.C4N232.valid⟩
  · exact ⟨FiniteK3Cases.C4N233.coeff,FiniteK3Cases.C4N233.valid⟩
  · exact ⟨FiniteK3Cases.C4N234.coeff,FiniteK3Cases.C4N234.valid⟩
  · exact ⟨FiniteK3Cases.C4N235.coeff,FiniteK3Cases.C4N235.valid⟩
  · exact ⟨FiniteK3Cases.C4N236.coeff,FiniteK3Cases.C4N236.valid⟩
  · exact ⟨FiniteK3Cases.C4N237.coeff,FiniteK3Cases.C4N237.valid⟩
  · exact ⟨FiniteK3Cases.C4N238.coeff,FiniteK3Cases.C4N238.valid⟩
  · exact ⟨FiniteK3Cases.C4N239.coeff,FiniteK3Cases.C4N239.valid⟩
  · exact ⟨FiniteK3Cases.C4N240.coeff,FiniteK3Cases.C4N240.valid⟩
  · exact ⟨FiniteK3Cases.C4N241.coeff,FiniteK3Cases.C4N241.valid⟩
  · exact ⟨FiniteK3Cases.C4N242.coeff,FiniteK3Cases.C4N242.valid⟩
  · exact ⟨FiniteK3Cases.C4N243.coeff,FiniteK3Cases.C4N243.valid⟩
  · exact ⟨FiniteK3Cases.C4N244.coeff,FiniteK3Cases.C4N244.valid⟩
  · exact ⟨FiniteK3Cases.C4N245.coeff,FiniteK3Cases.C4N245.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N230To245
