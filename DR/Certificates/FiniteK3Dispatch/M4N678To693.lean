import DR.Certificates.FiniteK3Cases.M4N678
import DR.Certificates.FiniteK3Cases.M4N679
import DR.Certificates.FiniteK3Cases.M4N680
import DR.Certificates.FiniteK3Cases.M4N681
import DR.Certificates.FiniteK3Cases.M4N682
import DR.Certificates.FiniteK3Cases.M4N683
import DR.Certificates.FiniteK3Cases.M4N684
import DR.Certificates.FiniteK3Cases.M4N685
import DR.Certificates.FiniteK3Cases.M4N686
import DR.Certificates.FiniteK3Cases.M4N687
import DR.Certificates.FiniteK3Cases.M4N688
import DR.Certificates.FiniteK3Cases.M4N689
import DR.Certificates.FiniteK3Cases.M4N690
import DR.Certificates.FiniteK3Cases.M4N691
import DR.Certificates.FiniteK3Cases.M4N692
import DR.Certificates.FiniteK3Cases.M4N693
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N678To693

theorem exists_valid (n : Nat) (hlo : 678≤n) (hhi : n≤693) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N678.coeff,FiniteK3Cases.C4N678.valid⟩
  · exact ⟨FiniteK3Cases.C4N679.coeff,FiniteK3Cases.C4N679.valid⟩
  · exact ⟨FiniteK3Cases.C4N680.coeff,FiniteK3Cases.C4N680.valid⟩
  · exact ⟨FiniteK3Cases.C4N681.coeff,FiniteK3Cases.C4N681.valid⟩
  · exact ⟨FiniteK3Cases.C4N682.coeff,FiniteK3Cases.C4N682.valid⟩
  · exact ⟨FiniteK3Cases.C4N683.coeff,FiniteK3Cases.C4N683.valid⟩
  · exact ⟨FiniteK3Cases.C4N684.coeff,FiniteK3Cases.C4N684.valid⟩
  · exact ⟨FiniteK3Cases.C4N685.coeff,FiniteK3Cases.C4N685.valid⟩
  · exact ⟨FiniteK3Cases.C4N686.coeff,FiniteK3Cases.C4N686.valid⟩
  · exact ⟨FiniteK3Cases.C4N687.coeff,FiniteK3Cases.C4N687.valid⟩
  · exact ⟨FiniteK3Cases.C4N688.coeff,FiniteK3Cases.C4N688.valid⟩
  · exact ⟨FiniteK3Cases.C4N689.coeff,FiniteK3Cases.C4N689.valid⟩
  · exact ⟨FiniteK3Cases.C4N690.coeff,FiniteK3Cases.C4N690.valid⟩
  · exact ⟨FiniteK3Cases.C4N691.coeff,FiniteK3Cases.C4N691.valid⟩
  · exact ⟨FiniteK3Cases.C4N692.coeff,FiniteK3Cases.C4N692.valid⟩
  · exact ⟨FiniteK3Cases.C4N693.coeff,FiniteK3Cases.C4N693.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N678To693
