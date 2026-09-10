import DR.Certificates.FiniteK3Cases.M4N502
import DR.Certificates.FiniteK3Cases.M4N503
import DR.Certificates.FiniteK3Cases.M4N504
import DR.Certificates.FiniteK3Cases.M4N505
import DR.Certificates.FiniteK3Cases.M4N506
import DR.Certificates.FiniteK3Cases.M4N507
import DR.Certificates.FiniteK3Cases.M4N508
import DR.Certificates.FiniteK3Cases.M4N509
import DR.Certificates.FiniteK3Cases.M4N510
import DR.Certificates.FiniteK3Cases.M4N511
import DR.Certificates.FiniteK3Cases.M4N512
import DR.Certificates.FiniteK3Cases.M4N513
import DR.Certificates.FiniteK3Cases.M4N514
import DR.Certificates.FiniteK3Cases.M4N515
import DR.Certificates.FiniteK3Cases.M4N516
import DR.Certificates.FiniteK3Cases.M4N517
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N502To517

theorem exists_valid (n : Nat) (hlo : 502≤n) (hhi : n≤517) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N502.coeff,FiniteK3Cases.C4N502.valid⟩
  · exact ⟨FiniteK3Cases.C4N503.coeff,FiniteK3Cases.C4N503.valid⟩
  · exact ⟨FiniteK3Cases.C4N504.coeff,FiniteK3Cases.C4N504.valid⟩
  · exact ⟨FiniteK3Cases.C4N505.coeff,FiniteK3Cases.C4N505.valid⟩
  · exact ⟨FiniteK3Cases.C4N506.coeff,FiniteK3Cases.C4N506.valid⟩
  · exact ⟨FiniteK3Cases.C4N507.coeff,FiniteK3Cases.C4N507.valid⟩
  · exact ⟨FiniteK3Cases.C4N508.coeff,FiniteK3Cases.C4N508.valid⟩
  · exact ⟨FiniteK3Cases.C4N509.coeff,FiniteK3Cases.C4N509.valid⟩
  · exact ⟨FiniteK3Cases.C4N510.coeff,FiniteK3Cases.C4N510.valid⟩
  · exact ⟨FiniteK3Cases.C4N511.coeff,FiniteK3Cases.C4N511.valid⟩
  · exact ⟨FiniteK3Cases.C4N512.coeff,FiniteK3Cases.C4N512.valid⟩
  · exact ⟨FiniteK3Cases.C4N513.coeff,FiniteK3Cases.C4N513.valid⟩
  · exact ⟨FiniteK3Cases.C4N514.coeff,FiniteK3Cases.C4N514.valid⟩
  · exact ⟨FiniteK3Cases.C4N515.coeff,FiniteK3Cases.C4N515.valid⟩
  · exact ⟨FiniteK3Cases.C4N516.coeff,FiniteK3Cases.C4N516.valid⟩
  · exact ⟨FiniteK3Cases.C4N517.coeff,FiniteK3Cases.C4N517.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N502To517
