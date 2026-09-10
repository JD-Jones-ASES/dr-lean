import DR.Certificates.FiniteK3Cases.M4N630
import DR.Certificates.FiniteK3Cases.M4N631
import DR.Certificates.FiniteK3Cases.M4N632
import DR.Certificates.FiniteK3Cases.M4N633
import DR.Certificates.FiniteK3Cases.M4N634
import DR.Certificates.FiniteK3Cases.M4N635
import DR.Certificates.FiniteK3Cases.M4N636
import DR.Certificates.FiniteK3Cases.M4N637
import DR.Certificates.FiniteK3Cases.M4N638
import DR.Certificates.FiniteK3Cases.M4N639
import DR.Certificates.FiniteK3Cases.M4N640
import DR.Certificates.FiniteK3Cases.M4N641
import DR.Certificates.FiniteK3Cases.M4N642
import DR.Certificates.FiniteK3Cases.M4N643
import DR.Certificates.FiniteK3Cases.M4N644
import DR.Certificates.FiniteK3Cases.M4N645
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N630To645

theorem exists_valid (n : Nat) (hlo : 630≤n) (hhi : n≤645) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N630.coeff,FiniteK3Cases.C4N630.valid⟩
  · exact ⟨FiniteK3Cases.C4N631.coeff,FiniteK3Cases.C4N631.valid⟩
  · exact ⟨FiniteK3Cases.C4N632.coeff,FiniteK3Cases.C4N632.valid⟩
  · exact ⟨FiniteK3Cases.C4N633.coeff,FiniteK3Cases.C4N633.valid⟩
  · exact ⟨FiniteK3Cases.C4N634.coeff,FiniteK3Cases.C4N634.valid⟩
  · exact ⟨FiniteK3Cases.C4N635.coeff,FiniteK3Cases.C4N635.valid⟩
  · exact ⟨FiniteK3Cases.C4N636.coeff,FiniteK3Cases.C4N636.valid⟩
  · exact ⟨FiniteK3Cases.C4N637.coeff,FiniteK3Cases.C4N637.valid⟩
  · exact ⟨FiniteK3Cases.C4N638.coeff,FiniteK3Cases.C4N638.valid⟩
  · exact ⟨FiniteK3Cases.C4N639.coeff,FiniteK3Cases.C4N639.valid⟩
  · exact ⟨FiniteK3Cases.C4N640.coeff,FiniteK3Cases.C4N640.valid⟩
  · exact ⟨FiniteK3Cases.C4N641.coeff,FiniteK3Cases.C4N641.valid⟩
  · exact ⟨FiniteK3Cases.C4N642.coeff,FiniteK3Cases.C4N642.valid⟩
  · exact ⟨FiniteK3Cases.C4N643.coeff,FiniteK3Cases.C4N643.valid⟩
  · exact ⟨FiniteK3Cases.C4N644.coeff,FiniteK3Cases.C4N644.valid⟩
  · exact ⟨FiniteK3Cases.C4N645.coeff,FiniteK3Cases.C4N645.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N630To645
