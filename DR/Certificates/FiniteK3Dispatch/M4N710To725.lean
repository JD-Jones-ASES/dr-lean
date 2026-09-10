import DR.Certificates.FiniteK3Cases.M4N710
import DR.Certificates.FiniteK3Cases.M4N711
import DR.Certificates.FiniteK3Cases.M4N712
import DR.Certificates.FiniteK3Cases.M4N713
import DR.Certificates.FiniteK3Cases.M4N714
import DR.Certificates.FiniteK3Cases.M4N715
import DR.Certificates.FiniteK3Cases.M4N716
import DR.Certificates.FiniteK3Cases.M4N717
import DR.Certificates.FiniteK3Cases.M4N718
import DR.Certificates.FiniteK3Cases.M4N719
import DR.Certificates.FiniteK3Cases.M4N720
import DR.Certificates.FiniteK3Cases.M4N721
import DR.Certificates.FiniteK3Cases.M4N722
import DR.Certificates.FiniteK3Cases.M4N723
import DR.Certificates.FiniteK3Cases.M4N724
import DR.Certificates.FiniteK3Cases.M4N725
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N710To725

theorem exists_valid (n : Nat) (hlo : 710≤n) (hhi : n≤725) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N710.coeff,FiniteK3Cases.C4N710.valid⟩
  · exact ⟨FiniteK3Cases.C4N711.coeff,FiniteK3Cases.C4N711.valid⟩
  · exact ⟨FiniteK3Cases.C4N712.coeff,FiniteK3Cases.C4N712.valid⟩
  · exact ⟨FiniteK3Cases.C4N713.coeff,FiniteK3Cases.C4N713.valid⟩
  · exact ⟨FiniteK3Cases.C4N714.coeff,FiniteK3Cases.C4N714.valid⟩
  · exact ⟨FiniteK3Cases.C4N715.coeff,FiniteK3Cases.C4N715.valid⟩
  · exact ⟨FiniteK3Cases.C4N716.coeff,FiniteK3Cases.C4N716.valid⟩
  · exact ⟨FiniteK3Cases.C4N717.coeff,FiniteK3Cases.C4N717.valid⟩
  · exact ⟨FiniteK3Cases.C4N718.coeff,FiniteK3Cases.C4N718.valid⟩
  · exact ⟨FiniteK3Cases.C4N719.coeff,FiniteK3Cases.C4N719.valid⟩
  · exact ⟨FiniteK3Cases.C4N720.coeff,FiniteK3Cases.C4N720.valid⟩
  · exact ⟨FiniteK3Cases.C4N721.coeff,FiniteK3Cases.C4N721.valid⟩
  · exact ⟨FiniteK3Cases.C4N722.coeff,FiniteK3Cases.C4N722.valid⟩
  · exact ⟨FiniteK3Cases.C4N723.coeff,FiniteK3Cases.C4N723.valid⟩
  · exact ⟨FiniteK3Cases.C4N724.coeff,FiniteK3Cases.C4N724.valid⟩
  · exact ⟨FiniteK3Cases.C4N725.coeff,FiniteK3Cases.C4N725.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N710To725
