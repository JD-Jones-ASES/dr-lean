import DR.Certificates.FiniteK3Cases.M4N278
import DR.Certificates.FiniteK3Cases.M4N279
import DR.Certificates.FiniteK3Cases.M4N280
import DR.Certificates.FiniteK3Cases.M4N281
import DR.Certificates.FiniteK3Cases.M4N282
import DR.Certificates.FiniteK3Cases.M4N283
import DR.Certificates.FiniteK3Cases.M4N284
import DR.Certificates.FiniteK3Cases.M4N285
import DR.Certificates.FiniteK3Cases.M4N286
import DR.Certificates.FiniteK3Cases.M4N287
import DR.Certificates.FiniteK3Cases.M4N288
import DR.Certificates.FiniteK3Cases.M4N289
import DR.Certificates.FiniteK3Cases.M4N290
import DR.Certificates.FiniteK3Cases.M4N291
import DR.Certificates.FiniteK3Cases.M4N292
import DR.Certificates.FiniteK3Cases.M4N293
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N278To293

theorem exists_valid (n : Nat) (hlo : 278≤n) (hhi : n≤293) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N278.coeff,FiniteK3Cases.C4N278.valid⟩
  · exact ⟨FiniteK3Cases.C4N279.coeff,FiniteK3Cases.C4N279.valid⟩
  · exact ⟨FiniteK3Cases.C4N280.coeff,FiniteK3Cases.C4N280.valid⟩
  · exact ⟨FiniteK3Cases.C4N281.coeff,FiniteK3Cases.C4N281.valid⟩
  · exact ⟨FiniteK3Cases.C4N282.coeff,FiniteK3Cases.C4N282.valid⟩
  · exact ⟨FiniteK3Cases.C4N283.coeff,FiniteK3Cases.C4N283.valid⟩
  · exact ⟨FiniteK3Cases.C4N284.coeff,FiniteK3Cases.C4N284.valid⟩
  · exact ⟨FiniteK3Cases.C4N285.coeff,FiniteK3Cases.C4N285.valid⟩
  · exact ⟨FiniteK3Cases.C4N286.coeff,FiniteK3Cases.C4N286.valid⟩
  · exact ⟨FiniteK3Cases.C4N287.coeff,FiniteK3Cases.C4N287.valid⟩
  · exact ⟨FiniteK3Cases.C4N288.coeff,FiniteK3Cases.C4N288.valid⟩
  · exact ⟨FiniteK3Cases.C4N289.coeff,FiniteK3Cases.C4N289.valid⟩
  · exact ⟨FiniteK3Cases.C4N290.coeff,FiniteK3Cases.C4N290.valid⟩
  · exact ⟨FiniteK3Cases.C4N291.coeff,FiniteK3Cases.C4N291.valid⟩
  · exact ⟨FiniteK3Cases.C4N292.coeff,FiniteK3Cases.C4N292.valid⟩
  · exact ⟨FiniteK3Cases.C4N293.coeff,FiniteK3Cases.C4N293.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N278To293
