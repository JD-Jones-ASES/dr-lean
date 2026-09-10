import DR.Certificates.FiniteK3Cases.M4N262
import DR.Certificates.FiniteK3Cases.M4N263
import DR.Certificates.FiniteK3Cases.M4N264
import DR.Certificates.FiniteK3Cases.M4N265
import DR.Certificates.FiniteK3Cases.M4N266
import DR.Certificates.FiniteK3Cases.M4N267
import DR.Certificates.FiniteK3Cases.M4N268
import DR.Certificates.FiniteK3Cases.M4N269
import DR.Certificates.FiniteK3Cases.M4N270
import DR.Certificates.FiniteK3Cases.M4N271
import DR.Certificates.FiniteK3Cases.M4N272
import DR.Certificates.FiniteK3Cases.M4N273
import DR.Certificates.FiniteK3Cases.M4N274
import DR.Certificates.FiniteK3Cases.M4N275
import DR.Certificates.FiniteK3Cases.M4N276
import DR.Certificates.FiniteK3Cases.M4N277
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N262To277

theorem exists_valid (n : Nat) (hlo : 262≤n) (hhi : n≤277) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N262.coeff,FiniteK3Cases.C4N262.valid⟩
  · exact ⟨FiniteK3Cases.C4N263.coeff,FiniteK3Cases.C4N263.valid⟩
  · exact ⟨FiniteK3Cases.C4N264.coeff,FiniteK3Cases.C4N264.valid⟩
  · exact ⟨FiniteK3Cases.C4N265.coeff,FiniteK3Cases.C4N265.valid⟩
  · exact ⟨FiniteK3Cases.C4N266.coeff,FiniteK3Cases.C4N266.valid⟩
  · exact ⟨FiniteK3Cases.C4N267.coeff,FiniteK3Cases.C4N267.valid⟩
  · exact ⟨FiniteK3Cases.C4N268.coeff,FiniteK3Cases.C4N268.valid⟩
  · exact ⟨FiniteK3Cases.C4N269.coeff,FiniteK3Cases.C4N269.valid⟩
  · exact ⟨FiniteK3Cases.C4N270.coeff,FiniteK3Cases.C4N270.valid⟩
  · exact ⟨FiniteK3Cases.C4N271.coeff,FiniteK3Cases.C4N271.valid⟩
  · exact ⟨FiniteK3Cases.C4N272.coeff,FiniteK3Cases.C4N272.valid⟩
  · exact ⟨FiniteK3Cases.C4N273.coeff,FiniteK3Cases.C4N273.valid⟩
  · exact ⟨FiniteK3Cases.C4N274.coeff,FiniteK3Cases.C4N274.valid⟩
  · exact ⟨FiniteK3Cases.C4N275.coeff,FiniteK3Cases.C4N275.valid⟩
  · exact ⟨FiniteK3Cases.C4N276.coeff,FiniteK3Cases.C4N276.valid⟩
  · exact ⟨FiniteK3Cases.C4N277.coeff,FiniteK3Cases.C4N277.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N262To277
