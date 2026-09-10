import DR.Certificates.FiniteK3Cases.M4N534
import DR.Certificates.FiniteK3Cases.M4N535
import DR.Certificates.FiniteK3Cases.M4N536
import DR.Certificates.FiniteK3Cases.M4N537
import DR.Certificates.FiniteK3Cases.M4N538
import DR.Certificates.FiniteK3Cases.M4N539
import DR.Certificates.FiniteK3Cases.M4N540
import DR.Certificates.FiniteK3Cases.M4N541
import DR.Certificates.FiniteK3Cases.M4N542
import DR.Certificates.FiniteK3Cases.M4N543
import DR.Certificates.FiniteK3Cases.M4N544
import DR.Certificates.FiniteK3Cases.M4N545
import DR.Certificates.FiniteK3Cases.M4N546
import DR.Certificates.FiniteK3Cases.M4N547
import DR.Certificates.FiniteK3Cases.M4N548
import DR.Certificates.FiniteK3Cases.M4N549
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N534To549

theorem exists_valid (n : Nat) (hlo : 534≤n) (hhi : n≤549) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N534.coeff,FiniteK3Cases.C4N534.valid⟩
  · exact ⟨FiniteK3Cases.C4N535.coeff,FiniteK3Cases.C4N535.valid⟩
  · exact ⟨FiniteK3Cases.C4N536.coeff,FiniteK3Cases.C4N536.valid⟩
  · exact ⟨FiniteK3Cases.C4N537.coeff,FiniteK3Cases.C4N537.valid⟩
  · exact ⟨FiniteK3Cases.C4N538.coeff,FiniteK3Cases.C4N538.valid⟩
  · exact ⟨FiniteK3Cases.C4N539.coeff,FiniteK3Cases.C4N539.valid⟩
  · exact ⟨FiniteK3Cases.C4N540.coeff,FiniteK3Cases.C4N540.valid⟩
  · exact ⟨FiniteK3Cases.C4N541.coeff,FiniteK3Cases.C4N541.valid⟩
  · exact ⟨FiniteK3Cases.C4N542.coeff,FiniteK3Cases.C4N542.valid⟩
  · exact ⟨FiniteK3Cases.C4N543.coeff,FiniteK3Cases.C4N543.valid⟩
  · exact ⟨FiniteK3Cases.C4N544.coeff,FiniteK3Cases.C4N544.valid⟩
  · exact ⟨FiniteK3Cases.C4N545.coeff,FiniteK3Cases.C4N545.valid⟩
  · exact ⟨FiniteK3Cases.C4N546.coeff,FiniteK3Cases.C4N546.valid⟩
  · exact ⟨FiniteK3Cases.C4N547.coeff,FiniteK3Cases.C4N547.valid⟩
  · exact ⟨FiniteK3Cases.C4N548.coeff,FiniteK3Cases.C4N548.valid⟩
  · exact ⟨FiniteK3Cases.C4N549.coeff,FiniteK3Cases.C4N549.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N534To549
