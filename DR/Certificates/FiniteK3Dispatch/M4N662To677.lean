import DR.Certificates.FiniteK3Cases.M4N662
import DR.Certificates.FiniteK3Cases.M4N663
import DR.Certificates.FiniteK3Cases.M4N664
import DR.Certificates.FiniteK3Cases.M4N665
import DR.Certificates.FiniteK3Cases.M4N666
import DR.Certificates.FiniteK3Cases.M4N667
import DR.Certificates.FiniteK3Cases.M4N668
import DR.Certificates.FiniteK3Cases.M4N669
import DR.Certificates.FiniteK3Cases.M4N670
import DR.Certificates.FiniteK3Cases.M4N671
import DR.Certificates.FiniteK3Cases.M4N672
import DR.Certificates.FiniteK3Cases.M4N673
import DR.Certificates.FiniteK3Cases.M4N674
import DR.Certificates.FiniteK3Cases.M4N675
import DR.Certificates.FiniteK3Cases.M4N676
import DR.Certificates.FiniteK3Cases.M4N677
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N662To677

theorem exists_valid (n : Nat) (hlo : 662≤n) (hhi : n≤677) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N662.coeff,FiniteK3Cases.C4N662.valid⟩
  · exact ⟨FiniteK3Cases.C4N663.coeff,FiniteK3Cases.C4N663.valid⟩
  · exact ⟨FiniteK3Cases.C4N664.coeff,FiniteK3Cases.C4N664.valid⟩
  · exact ⟨FiniteK3Cases.C4N665.coeff,FiniteK3Cases.C4N665.valid⟩
  · exact ⟨FiniteK3Cases.C4N666.coeff,FiniteK3Cases.C4N666.valid⟩
  · exact ⟨FiniteK3Cases.C4N667.coeff,FiniteK3Cases.C4N667.valid⟩
  · exact ⟨FiniteK3Cases.C4N668.coeff,FiniteK3Cases.C4N668.valid⟩
  · exact ⟨FiniteK3Cases.C4N669.coeff,FiniteK3Cases.C4N669.valid⟩
  · exact ⟨FiniteK3Cases.C4N670.coeff,FiniteK3Cases.C4N670.valid⟩
  · exact ⟨FiniteK3Cases.C4N671.coeff,FiniteK3Cases.C4N671.valid⟩
  · exact ⟨FiniteK3Cases.C4N672.coeff,FiniteK3Cases.C4N672.valid⟩
  · exact ⟨FiniteK3Cases.C4N673.coeff,FiniteK3Cases.C4N673.valid⟩
  · exact ⟨FiniteK3Cases.C4N674.coeff,FiniteK3Cases.C4N674.valid⟩
  · exact ⟨FiniteK3Cases.C4N675.coeff,FiniteK3Cases.C4N675.valid⟩
  · exact ⟨FiniteK3Cases.C4N676.coeff,FiniteK3Cases.C4N676.valid⟩
  · exact ⟨FiniteK3Cases.C4N677.coeff,FiniteK3Cases.C4N677.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N662To677
