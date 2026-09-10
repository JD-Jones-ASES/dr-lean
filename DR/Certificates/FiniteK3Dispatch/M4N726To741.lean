import DR.Certificates.FiniteK3Cases.M4N726
import DR.Certificates.FiniteK3Cases.M4N727
import DR.Certificates.FiniteK3Cases.M4N728
import DR.Certificates.FiniteK3Cases.M4N729
import DR.Certificates.FiniteK3Cases.M4N730
import DR.Certificates.FiniteK3Cases.M4N731
import DR.Certificates.FiniteK3Cases.M4N732
import DR.Certificates.FiniteK3Cases.M4N733
import DR.Certificates.FiniteK3Cases.M4N734
import DR.Certificates.FiniteK3Cases.M4N735
import DR.Certificates.FiniteK3Cases.M4N736
import DR.Certificates.FiniteK3Cases.M4N737
import DR.Certificates.FiniteK3Cases.M4N738
import DR.Certificates.FiniteK3Cases.M4N739
import DR.Certificates.FiniteK3Cases.M4N740
import DR.Certificates.FiniteK3Cases.M4N741
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N726To741

theorem exists_valid (n : Nat) (hlo : 726≤n) (hhi : n≤741) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N726.coeff,FiniteK3Cases.C4N726.valid⟩
  · exact ⟨FiniteK3Cases.C4N727.coeff,FiniteK3Cases.C4N727.valid⟩
  · exact ⟨FiniteK3Cases.C4N728.coeff,FiniteK3Cases.C4N728.valid⟩
  · exact ⟨FiniteK3Cases.C4N729.coeff,FiniteK3Cases.C4N729.valid⟩
  · exact ⟨FiniteK3Cases.C4N730.coeff,FiniteK3Cases.C4N730.valid⟩
  · exact ⟨FiniteK3Cases.C4N731.coeff,FiniteK3Cases.C4N731.valid⟩
  · exact ⟨FiniteK3Cases.C4N732.coeff,FiniteK3Cases.C4N732.valid⟩
  · exact ⟨FiniteK3Cases.C4N733.coeff,FiniteK3Cases.C4N733.valid⟩
  · exact ⟨FiniteK3Cases.C4N734.coeff,FiniteK3Cases.C4N734.valid⟩
  · exact ⟨FiniteK3Cases.C4N735.coeff,FiniteK3Cases.C4N735.valid⟩
  · exact ⟨FiniteK3Cases.C4N736.coeff,FiniteK3Cases.C4N736.valid⟩
  · exact ⟨FiniteK3Cases.C4N737.coeff,FiniteK3Cases.C4N737.valid⟩
  · exact ⟨FiniteK3Cases.C4N738.coeff,FiniteK3Cases.C4N738.valid⟩
  · exact ⟨FiniteK3Cases.C4N739.coeff,FiniteK3Cases.C4N739.valid⟩
  · exact ⟨FiniteK3Cases.C4N740.coeff,FiniteK3Cases.C4N740.valid⟩
  · exact ⟨FiniteK3Cases.C4N741.coeff,FiniteK3Cases.C4N741.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N726To741
