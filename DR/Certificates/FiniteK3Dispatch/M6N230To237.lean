import DR.Certificates.FiniteK3Cases.M6N230
import DR.Certificates.FiniteK3Cases.M6N231
import DR.Certificates.FiniteK3Cases.M6N232
import DR.Certificates.FiniteK3Cases.M6N233
import DR.Certificates.FiniteK3Cases.M6N234
import DR.Certificates.FiniteK3Cases.M6N235
import DR.Certificates.FiniteK3Cases.M6N236
import DR.Certificates.FiniteK3Cases.M6N237
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N230To237

theorem exists_valid (n : Nat) (hlo : 230≤n) (hhi : n≤237) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N230.coeff,FiniteK3Cases.C6N230.valid⟩
  · exact ⟨FiniteK3Cases.C6N231.coeff,FiniteK3Cases.C6N231.valid⟩
  · exact ⟨FiniteK3Cases.C6N232.coeff,FiniteK3Cases.C6N232.valid⟩
  · exact ⟨FiniteK3Cases.C6N233.coeff,FiniteK3Cases.C6N233.valid⟩
  · exact ⟨FiniteK3Cases.C6N234.coeff,FiniteK3Cases.C6N234.valid⟩
  · exact ⟨FiniteK3Cases.C6N235.coeff,FiniteK3Cases.C6N235.valid⟩
  · exact ⟨FiniteK3Cases.C6N236.coeff,FiniteK3Cases.C6N236.valid⟩
  · exact ⟨FiniteK3Cases.C6N237.coeff,FiniteK3Cases.C6N237.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N230To237
