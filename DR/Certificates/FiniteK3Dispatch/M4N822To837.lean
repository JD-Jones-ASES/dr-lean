import DR.Certificates.FiniteK3Cases.M4N822
import DR.Certificates.FiniteK3Cases.M4N823
import DR.Certificates.FiniteK3Cases.M4N824
import DR.Certificates.FiniteK3Cases.M4N825
import DR.Certificates.FiniteK3Cases.M4N826
import DR.Certificates.FiniteK3Cases.M4N827
import DR.Certificates.FiniteK3Cases.M4N828
import DR.Certificates.FiniteK3Cases.M4N829
import DR.Certificates.FiniteK3Cases.M4N830
import DR.Certificates.FiniteK3Cases.M4N831
import DR.Certificates.FiniteK3Cases.M4N832
import DR.Certificates.FiniteK3Cases.M4N833
import DR.Certificates.FiniteK3Cases.M4N834
import DR.Certificates.FiniteK3Cases.M4N835
import DR.Certificates.FiniteK3Cases.M4N836
import DR.Certificates.FiniteK3Cases.M4N837
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N822To837

theorem exists_valid (n : Nat) (hlo : 822≤n) (hhi : n≤837) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N822.coeff,FiniteK3Cases.C4N822.valid⟩
  · exact ⟨FiniteK3Cases.C4N823.coeff,FiniteK3Cases.C4N823.valid⟩
  · exact ⟨FiniteK3Cases.C4N824.coeff,FiniteK3Cases.C4N824.valid⟩
  · exact ⟨FiniteK3Cases.C4N825.coeff,FiniteK3Cases.C4N825.valid⟩
  · exact ⟨FiniteK3Cases.C4N826.coeff,FiniteK3Cases.C4N826.valid⟩
  · exact ⟨FiniteK3Cases.C4N827.coeff,FiniteK3Cases.C4N827.valid⟩
  · exact ⟨FiniteK3Cases.C4N828.coeff,FiniteK3Cases.C4N828.valid⟩
  · exact ⟨FiniteK3Cases.C4N829.coeff,FiniteK3Cases.C4N829.valid⟩
  · exact ⟨FiniteK3Cases.C4N830.coeff,FiniteK3Cases.C4N830.valid⟩
  · exact ⟨FiniteK3Cases.C4N831.coeff,FiniteK3Cases.C4N831.valid⟩
  · exact ⟨FiniteK3Cases.C4N832.coeff,FiniteK3Cases.C4N832.valid⟩
  · exact ⟨FiniteK3Cases.C4N833.coeff,FiniteK3Cases.C4N833.valid⟩
  · exact ⟨FiniteK3Cases.C4N834.coeff,FiniteK3Cases.C4N834.valid⟩
  · exact ⟨FiniteK3Cases.C4N835.coeff,FiniteK3Cases.C4N835.valid⟩
  · exact ⟨FiniteK3Cases.C4N836.coeff,FiniteK3Cases.C4N836.valid⟩
  · exact ⟨FiniteK3Cases.C4N837.coeff,FiniteK3Cases.C4N837.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N822To837
