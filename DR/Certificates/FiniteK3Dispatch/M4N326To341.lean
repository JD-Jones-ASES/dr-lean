import DR.Certificates.FiniteK3Cases.M4N326
import DR.Certificates.FiniteK3Cases.M4N327
import DR.Certificates.FiniteK3Cases.M4N328
import DR.Certificates.FiniteK3Cases.M4N329
import DR.Certificates.FiniteK3Cases.M4N330
import DR.Certificates.FiniteK3Cases.M4N331
import DR.Certificates.FiniteK3Cases.M4N332
import DR.Certificates.FiniteK3Cases.M4N333
import DR.Certificates.FiniteK3Cases.M4N334
import DR.Certificates.FiniteK3Cases.M4N335
import DR.Certificates.FiniteK3Cases.M4N336
import DR.Certificates.FiniteK3Cases.M4N337
import DR.Certificates.FiniteK3Cases.M4N338
import DR.Certificates.FiniteK3Cases.M4N339
import DR.Certificates.FiniteK3Cases.M4N340
import DR.Certificates.FiniteK3Cases.M4N341
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N326To341

theorem exists_valid (n : Nat) (hlo : 326≤n) (hhi : n≤341) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N326.coeff,FiniteK3Cases.C4N326.valid⟩
  · exact ⟨FiniteK3Cases.C4N327.coeff,FiniteK3Cases.C4N327.valid⟩
  · exact ⟨FiniteK3Cases.C4N328.coeff,FiniteK3Cases.C4N328.valid⟩
  · exact ⟨FiniteK3Cases.C4N329.coeff,FiniteK3Cases.C4N329.valid⟩
  · exact ⟨FiniteK3Cases.C4N330.coeff,FiniteK3Cases.C4N330.valid⟩
  · exact ⟨FiniteK3Cases.C4N331.coeff,FiniteK3Cases.C4N331.valid⟩
  · exact ⟨FiniteK3Cases.C4N332.coeff,FiniteK3Cases.C4N332.valid⟩
  · exact ⟨FiniteK3Cases.C4N333.coeff,FiniteK3Cases.C4N333.valid⟩
  · exact ⟨FiniteK3Cases.C4N334.coeff,FiniteK3Cases.C4N334.valid⟩
  · exact ⟨FiniteK3Cases.C4N335.coeff,FiniteK3Cases.C4N335.valid⟩
  · exact ⟨FiniteK3Cases.C4N336.coeff,FiniteK3Cases.C4N336.valid⟩
  · exact ⟨FiniteK3Cases.C4N337.coeff,FiniteK3Cases.C4N337.valid⟩
  · exact ⟨FiniteK3Cases.C4N338.coeff,FiniteK3Cases.C4N338.valid⟩
  · exact ⟨FiniteK3Cases.C4N339.coeff,FiniteK3Cases.C4N339.valid⟩
  · exact ⟨FiniteK3Cases.C4N340.coeff,FiniteK3Cases.C4N340.valid⟩
  · exact ⟨FiniteK3Cases.C4N341.coeff,FiniteK3Cases.C4N341.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N326To341
