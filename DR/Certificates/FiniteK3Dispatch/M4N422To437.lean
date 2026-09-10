import DR.Certificates.FiniteK3Cases.M4N422
import DR.Certificates.FiniteK3Cases.M4N423
import DR.Certificates.FiniteK3Cases.M4N424
import DR.Certificates.FiniteK3Cases.M4N425
import DR.Certificates.FiniteK3Cases.M4N426
import DR.Certificates.FiniteK3Cases.M4N427
import DR.Certificates.FiniteK3Cases.M4N428
import DR.Certificates.FiniteK3Cases.M4N429
import DR.Certificates.FiniteK3Cases.M4N430
import DR.Certificates.FiniteK3Cases.M4N431
import DR.Certificates.FiniteK3Cases.M4N432
import DR.Certificates.FiniteK3Cases.M4N433
import DR.Certificates.FiniteK3Cases.M4N434
import DR.Certificates.FiniteK3Cases.M4N435
import DR.Certificates.FiniteK3Cases.M4N436
import DR.Certificates.FiniteK3Cases.M4N437
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N422To437

theorem exists_valid (n : Nat) (hlo : 422≤n) (hhi : n≤437) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N422.coeff,FiniteK3Cases.C4N422.valid⟩
  · exact ⟨FiniteK3Cases.C4N423.coeff,FiniteK3Cases.C4N423.valid⟩
  · exact ⟨FiniteK3Cases.C4N424.coeff,FiniteK3Cases.C4N424.valid⟩
  · exact ⟨FiniteK3Cases.C4N425.coeff,FiniteK3Cases.C4N425.valid⟩
  · exact ⟨FiniteK3Cases.C4N426.coeff,FiniteK3Cases.C4N426.valid⟩
  · exact ⟨FiniteK3Cases.C4N427.coeff,FiniteK3Cases.C4N427.valid⟩
  · exact ⟨FiniteK3Cases.C4N428.coeff,FiniteK3Cases.C4N428.valid⟩
  · exact ⟨FiniteK3Cases.C4N429.coeff,FiniteK3Cases.C4N429.valid⟩
  · exact ⟨FiniteK3Cases.C4N430.coeff,FiniteK3Cases.C4N430.valid⟩
  · exact ⟨FiniteK3Cases.C4N431.coeff,FiniteK3Cases.C4N431.valid⟩
  · exact ⟨FiniteK3Cases.C4N432.coeff,FiniteK3Cases.C4N432.valid⟩
  · exact ⟨FiniteK3Cases.C4N433.coeff,FiniteK3Cases.C4N433.valid⟩
  · exact ⟨FiniteK3Cases.C4N434.coeff,FiniteK3Cases.C4N434.valid⟩
  · exact ⟨FiniteK3Cases.C4N435.coeff,FiniteK3Cases.C4N435.valid⟩
  · exact ⟨FiniteK3Cases.C4N436.coeff,FiniteK3Cases.C4N436.valid⟩
  · exact ⟨FiniteK3Cases.C4N437.coeff,FiniteK3Cases.C4N437.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N422To437
