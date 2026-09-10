import DR.Certificates.FiniteK3Cases.M4N742
import DR.Certificates.FiniteK3Cases.M4N743
import DR.Certificates.FiniteK3Cases.M4N744
import DR.Certificates.FiniteK3Cases.M4N745
import DR.Certificates.FiniteK3Cases.M4N746
import DR.Certificates.FiniteK3Cases.M4N747
import DR.Certificates.FiniteK3Cases.M4N748
import DR.Certificates.FiniteK3Cases.M4N749
import DR.Certificates.FiniteK3Cases.M4N750
import DR.Certificates.FiniteK3Cases.M4N751
import DR.Certificates.FiniteK3Cases.M4N752
import DR.Certificates.FiniteK3Cases.M4N753
import DR.Certificates.FiniteK3Cases.M4N754
import DR.Certificates.FiniteK3Cases.M4N755
import DR.Certificates.FiniteK3Cases.M4N756
import DR.Certificates.FiniteK3Cases.M4N757
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N742To757

theorem exists_valid (n : Nat) (hlo : 742≤n) (hhi : n≤757) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N742.coeff,FiniteK3Cases.C4N742.valid⟩
  · exact ⟨FiniteK3Cases.C4N743.coeff,FiniteK3Cases.C4N743.valid⟩
  · exact ⟨FiniteK3Cases.C4N744.coeff,FiniteK3Cases.C4N744.valid⟩
  · exact ⟨FiniteK3Cases.C4N745.coeff,FiniteK3Cases.C4N745.valid⟩
  · exact ⟨FiniteK3Cases.C4N746.coeff,FiniteK3Cases.C4N746.valid⟩
  · exact ⟨FiniteK3Cases.C4N747.coeff,FiniteK3Cases.C4N747.valid⟩
  · exact ⟨FiniteK3Cases.C4N748.coeff,FiniteK3Cases.C4N748.valid⟩
  · exact ⟨FiniteK3Cases.C4N749.coeff,FiniteK3Cases.C4N749.valid⟩
  · exact ⟨FiniteK3Cases.C4N750.coeff,FiniteK3Cases.C4N750.valid⟩
  · exact ⟨FiniteK3Cases.C4N751.coeff,FiniteK3Cases.C4N751.valid⟩
  · exact ⟨FiniteK3Cases.C4N752.coeff,FiniteK3Cases.C4N752.valid⟩
  · exact ⟨FiniteK3Cases.C4N753.coeff,FiniteK3Cases.C4N753.valid⟩
  · exact ⟨FiniteK3Cases.C4N754.coeff,FiniteK3Cases.C4N754.valid⟩
  · exact ⟨FiniteK3Cases.C4N755.coeff,FiniteK3Cases.C4N755.valid⟩
  · exact ⟨FiniteK3Cases.C4N756.coeff,FiniteK3Cases.C4N756.valid⟩
  · exact ⟨FiniteK3Cases.C4N757.coeff,FiniteK3Cases.C4N757.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N742To757
