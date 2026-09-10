import DR.Certificates.FiniteK3Cases.M7N23
import DR.Certificates.FiniteK3Cases.M7N24
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C7N23To24

theorem exists_valid (n : Nat) (hlo : 23≤n) (hhi : n≤24) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 7 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C7N23.coeff,FiniteK3Cases.C7N23.valid⟩
  · exact ⟨FiniteK3Cases.C7N24.coeff,FiniteK3Cases.C7N24.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C7N23To24
