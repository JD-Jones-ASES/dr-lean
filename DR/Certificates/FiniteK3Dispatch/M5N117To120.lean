import DR.Certificates.FiniteK3Cases.M5N117
import DR.Certificates.FiniteK3Cases.M5N118
import DR.Certificates.FiniteK3Cases.M5N119
import DR.Certificates.FiniteK3Cases.M5N120
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N117To120

theorem exists_valid (n : Nat) (hlo : 117≤n) (hhi : n≤120) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N117.coeff,FiniteK3Cases.C5N117.valid⟩
  · exact ⟨FiniteK3Cases.C5N118.coeff,FiniteK3Cases.C5N118.valid⟩
  · exact ⟨FiniteK3Cases.C5N119.coeff,FiniteK3Cases.C5N119.valid⟩
  · exact ⟨FiniteK3Cases.C5N120.coeff,FiniteK3Cases.C5N120.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N117To120
