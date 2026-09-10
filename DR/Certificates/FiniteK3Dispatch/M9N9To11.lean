import DR.Certificates.FiniteK3Cases.M9N9
import DR.Certificates.FiniteK3Cases.M9N10
import DR.Certificates.FiniteK3Cases.M9N11
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C9N9To11

theorem exists_valid (n : Nat) (hlo : 9≤n) (hhi : n≤11) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 9 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C9N9.coeff,FiniteK3Cases.C9N9.valid⟩
  · exact ⟨FiniteK3Cases.C9N10.coeff,FiniteK3Cases.C9N10.valid⟩
  · exact ⟨FiniteK3Cases.C9N11.coeff,FiniteK3Cases.C9N11.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C9N9To11
