import DR.Certificates.FiniteK3Cases.M4N294
import DR.Certificates.FiniteK3Cases.M4N295
import DR.Certificates.FiniteK3Cases.M4N296
import DR.Certificates.FiniteK3Cases.M4N297
import DR.Certificates.FiniteK3Cases.M4N298
import DR.Certificates.FiniteK3Cases.M4N299
import DR.Certificates.FiniteK3Cases.M4N300
import DR.Certificates.FiniteK3Cases.M4N301
import DR.Certificates.FiniteK3Cases.M4N302
import DR.Certificates.FiniteK3Cases.M4N303
import DR.Certificates.FiniteK3Cases.M4N304
import DR.Certificates.FiniteK3Cases.M4N305
import DR.Certificates.FiniteK3Cases.M4N306
import DR.Certificates.FiniteK3Cases.M4N307
import DR.Certificates.FiniteK3Cases.M4N308
import DR.Certificates.FiniteK3Cases.M4N309
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N294To309

theorem exists_valid (n : Nat) (hlo : 294≤n) (hhi : n≤309) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N294.coeff,FiniteK3Cases.C4N294.valid⟩
  · exact ⟨FiniteK3Cases.C4N295.coeff,FiniteK3Cases.C4N295.valid⟩
  · exact ⟨FiniteK3Cases.C4N296.coeff,FiniteK3Cases.C4N296.valid⟩
  · exact ⟨FiniteK3Cases.C4N297.coeff,FiniteK3Cases.C4N297.valid⟩
  · exact ⟨FiniteK3Cases.C4N298.coeff,FiniteK3Cases.C4N298.valid⟩
  · exact ⟨FiniteK3Cases.C4N299.coeff,FiniteK3Cases.C4N299.valid⟩
  · exact ⟨FiniteK3Cases.C4N300.coeff,FiniteK3Cases.C4N300.valid⟩
  · exact ⟨FiniteK3Cases.C4N301.coeff,FiniteK3Cases.C4N301.valid⟩
  · exact ⟨FiniteK3Cases.C4N302.coeff,FiniteK3Cases.C4N302.valid⟩
  · exact ⟨FiniteK3Cases.C4N303.coeff,FiniteK3Cases.C4N303.valid⟩
  · exact ⟨FiniteK3Cases.C4N304.coeff,FiniteK3Cases.C4N304.valid⟩
  · exact ⟨FiniteK3Cases.C4N305.coeff,FiniteK3Cases.C4N305.valid⟩
  · exact ⟨FiniteK3Cases.C4N306.coeff,FiniteK3Cases.C4N306.valid⟩
  · exact ⟨FiniteK3Cases.C4N307.coeff,FiniteK3Cases.C4N307.valid⟩
  · exact ⟨FiniteK3Cases.C4N308.coeff,FiniteK3Cases.C4N308.valid⟩
  · exact ⟨FiniteK3Cases.C4N309.coeff,FiniteK3Cases.C4N309.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N294To309
