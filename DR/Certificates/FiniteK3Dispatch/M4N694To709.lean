import DR.Certificates.FiniteK3Cases.M4N694
import DR.Certificates.FiniteK3Cases.M4N695
import DR.Certificates.FiniteK3Cases.M4N696
import DR.Certificates.FiniteK3Cases.M4N697
import DR.Certificates.FiniteK3Cases.M4N698
import DR.Certificates.FiniteK3Cases.M4N699
import DR.Certificates.FiniteK3Cases.M4N700
import DR.Certificates.FiniteK3Cases.M4N701
import DR.Certificates.FiniteK3Cases.M4N702
import DR.Certificates.FiniteK3Cases.M4N703
import DR.Certificates.FiniteK3Cases.M4N704
import DR.Certificates.FiniteK3Cases.M4N705
import DR.Certificates.FiniteK3Cases.M4N706
import DR.Certificates.FiniteK3Cases.M4N707
import DR.Certificates.FiniteK3Cases.M4N708
import DR.Certificates.FiniteK3Cases.M4N709
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N694To709

theorem exists_valid (n : Nat) (hlo : 694≤n) (hhi : n≤709) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N694.coeff,FiniteK3Cases.C4N694.valid⟩
  · exact ⟨FiniteK3Cases.C4N695.coeff,FiniteK3Cases.C4N695.valid⟩
  · exact ⟨FiniteK3Cases.C4N696.coeff,FiniteK3Cases.C4N696.valid⟩
  · exact ⟨FiniteK3Cases.C4N697.coeff,FiniteK3Cases.C4N697.valid⟩
  · exact ⟨FiniteK3Cases.C4N698.coeff,FiniteK3Cases.C4N698.valid⟩
  · exact ⟨FiniteK3Cases.C4N699.coeff,FiniteK3Cases.C4N699.valid⟩
  · exact ⟨FiniteK3Cases.C4N700.coeff,FiniteK3Cases.C4N700.valid⟩
  · exact ⟨FiniteK3Cases.C4N701.coeff,FiniteK3Cases.C4N701.valid⟩
  · exact ⟨FiniteK3Cases.C4N702.coeff,FiniteK3Cases.C4N702.valid⟩
  · exact ⟨FiniteK3Cases.C4N703.coeff,FiniteK3Cases.C4N703.valid⟩
  · exact ⟨FiniteK3Cases.C4N704.coeff,FiniteK3Cases.C4N704.valid⟩
  · exact ⟨FiniteK3Cases.C4N705.coeff,FiniteK3Cases.C4N705.valid⟩
  · exact ⟨FiniteK3Cases.C4N706.coeff,FiniteK3Cases.C4N706.valid⟩
  · exact ⟨FiniteK3Cases.C4N707.coeff,FiniteK3Cases.C4N707.valid⟩
  · exact ⟨FiniteK3Cases.C4N708.coeff,FiniteK3Cases.C4N708.valid⟩
  · exact ⟨FiniteK3Cases.C4N709.coeff,FiniteK3Cases.C4N709.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N694To709
