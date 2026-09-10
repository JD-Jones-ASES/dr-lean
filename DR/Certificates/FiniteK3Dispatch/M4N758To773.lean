import DR.Certificates.FiniteK3Cases.M4N758
import DR.Certificates.FiniteK3Cases.M4N759
import DR.Certificates.FiniteK3Cases.M4N760
import DR.Certificates.FiniteK3Cases.M4N761
import DR.Certificates.FiniteK3Cases.M4N762
import DR.Certificates.FiniteK3Cases.M4N763
import DR.Certificates.FiniteK3Cases.M4N764
import DR.Certificates.FiniteK3Cases.M4N765
import DR.Certificates.FiniteK3Cases.M4N766
import DR.Certificates.FiniteK3Cases.M4N767
import DR.Certificates.FiniteK3Cases.M4N768
import DR.Certificates.FiniteK3Cases.M4N769
import DR.Certificates.FiniteK3Cases.M4N770
import DR.Certificates.FiniteK3Cases.M4N771
import DR.Certificates.FiniteK3Cases.M4N772
import DR.Certificates.FiniteK3Cases.M4N773
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N758To773

theorem exists_valid (n : Nat) (hlo : 758≤n) (hhi : n≤773) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N758.coeff,FiniteK3Cases.C4N758.valid⟩
  · exact ⟨FiniteK3Cases.C4N759.coeff,FiniteK3Cases.C4N759.valid⟩
  · exact ⟨FiniteK3Cases.C4N760.coeff,FiniteK3Cases.C4N760.valid⟩
  · exact ⟨FiniteK3Cases.C4N761.coeff,FiniteK3Cases.C4N761.valid⟩
  · exact ⟨FiniteK3Cases.C4N762.coeff,FiniteK3Cases.C4N762.valid⟩
  · exact ⟨FiniteK3Cases.C4N763.coeff,FiniteK3Cases.C4N763.valid⟩
  · exact ⟨FiniteK3Cases.C4N764.coeff,FiniteK3Cases.C4N764.valid⟩
  · exact ⟨FiniteK3Cases.C4N765.coeff,FiniteK3Cases.C4N765.valid⟩
  · exact ⟨FiniteK3Cases.C4N766.coeff,FiniteK3Cases.C4N766.valid⟩
  · exact ⟨FiniteK3Cases.C4N767.coeff,FiniteK3Cases.C4N767.valid⟩
  · exact ⟨FiniteK3Cases.C4N768.coeff,FiniteK3Cases.C4N768.valid⟩
  · exact ⟨FiniteK3Cases.C4N769.coeff,FiniteK3Cases.C4N769.valid⟩
  · exact ⟨FiniteK3Cases.C4N770.coeff,FiniteK3Cases.C4N770.valid⟩
  · exact ⟨FiniteK3Cases.C4N771.coeff,FiniteK3Cases.C4N771.valid⟩
  · exact ⟨FiniteK3Cases.C4N772.coeff,FiniteK3Cases.C4N772.valid⟩
  · exact ⟨FiniteK3Cases.C4N773.coeff,FiniteK3Cases.C4N773.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N758To773
