import DR.Certificates.FiniteK3Cases.M4N646
import DR.Certificates.FiniteK3Cases.M4N647
import DR.Certificates.FiniteK3Cases.M4N648
import DR.Certificates.FiniteK3Cases.M4N649
import DR.Certificates.FiniteK3Cases.M4N650
import DR.Certificates.FiniteK3Cases.M4N651
import DR.Certificates.FiniteK3Cases.M4N652
import DR.Certificates.FiniteK3Cases.M4N653
import DR.Certificates.FiniteK3Cases.M4N654
import DR.Certificates.FiniteK3Cases.M4N655
import DR.Certificates.FiniteK3Cases.M4N656
import DR.Certificates.FiniteK3Cases.M4N657
import DR.Certificates.FiniteK3Cases.M4N658
import DR.Certificates.FiniteK3Cases.M4N659
import DR.Certificates.FiniteK3Cases.M4N660
import DR.Certificates.FiniteK3Cases.M4N661
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N646To661

theorem exists_valid (n : Nat) (hlo : 646≤n) (hhi : n≤661) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N646.coeff,FiniteK3Cases.C4N646.valid⟩
  · exact ⟨FiniteK3Cases.C4N647.coeff,FiniteK3Cases.C4N647.valid⟩
  · exact ⟨FiniteK3Cases.C4N648.coeff,FiniteK3Cases.C4N648.valid⟩
  · exact ⟨FiniteK3Cases.C4N649.coeff,FiniteK3Cases.C4N649.valid⟩
  · exact ⟨FiniteK3Cases.C4N650.coeff,FiniteK3Cases.C4N650.valid⟩
  · exact ⟨FiniteK3Cases.C4N651.coeff,FiniteK3Cases.C4N651.valid⟩
  · exact ⟨FiniteK3Cases.C4N652.coeff,FiniteK3Cases.C4N652.valid⟩
  · exact ⟨FiniteK3Cases.C4N653.coeff,FiniteK3Cases.C4N653.valid⟩
  · exact ⟨FiniteK3Cases.C4N654.coeff,FiniteK3Cases.C4N654.valid⟩
  · exact ⟨FiniteK3Cases.C4N655.coeff,FiniteK3Cases.C4N655.valid⟩
  · exact ⟨FiniteK3Cases.C4N656.coeff,FiniteK3Cases.C4N656.valid⟩
  · exact ⟨FiniteK3Cases.C4N657.coeff,FiniteK3Cases.C4N657.valid⟩
  · exact ⟨FiniteK3Cases.C4N658.coeff,FiniteK3Cases.C4N658.valid⟩
  · exact ⟨FiniteK3Cases.C4N659.coeff,FiniteK3Cases.C4N659.valid⟩
  · exact ⟨FiniteK3Cases.C4N660.coeff,FiniteK3Cases.C4N660.valid⟩
  · exact ⟨FiniteK3Cases.C4N661.coeff,FiniteK3Cases.C4N661.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N646To661
