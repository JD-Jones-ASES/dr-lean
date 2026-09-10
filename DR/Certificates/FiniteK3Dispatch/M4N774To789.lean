import DR.Certificates.FiniteK3Cases.M4N774
import DR.Certificates.FiniteK3Cases.M4N775
import DR.Certificates.FiniteK3Cases.M4N776
import DR.Certificates.FiniteK3Cases.M4N777
import DR.Certificates.FiniteK3Cases.M4N778
import DR.Certificates.FiniteK3Cases.M4N779
import DR.Certificates.FiniteK3Cases.M4N780
import DR.Certificates.FiniteK3Cases.M4N781
import DR.Certificates.FiniteK3Cases.M4N782
import DR.Certificates.FiniteK3Cases.M4N783
import DR.Certificates.FiniteK3Cases.M4N784
import DR.Certificates.FiniteK3Cases.M4N785
import DR.Certificates.FiniteK3Cases.M4N786
import DR.Certificates.FiniteK3Cases.M4N787
import DR.Certificates.FiniteK3Cases.M4N788
import DR.Certificates.FiniteK3Cases.M4N789
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N774To789

theorem exists_valid (n : Nat) (hlo : 774≤n) (hhi : n≤789) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N774.coeff,FiniteK3Cases.C4N774.valid⟩
  · exact ⟨FiniteK3Cases.C4N775.coeff,FiniteK3Cases.C4N775.valid⟩
  · exact ⟨FiniteK3Cases.C4N776.coeff,FiniteK3Cases.C4N776.valid⟩
  · exact ⟨FiniteK3Cases.C4N777.coeff,FiniteK3Cases.C4N777.valid⟩
  · exact ⟨FiniteK3Cases.C4N778.coeff,FiniteK3Cases.C4N778.valid⟩
  · exact ⟨FiniteK3Cases.C4N779.coeff,FiniteK3Cases.C4N779.valid⟩
  · exact ⟨FiniteK3Cases.C4N780.coeff,FiniteK3Cases.C4N780.valid⟩
  · exact ⟨FiniteK3Cases.C4N781.coeff,FiniteK3Cases.C4N781.valid⟩
  · exact ⟨FiniteK3Cases.C4N782.coeff,FiniteK3Cases.C4N782.valid⟩
  · exact ⟨FiniteK3Cases.C4N783.coeff,FiniteK3Cases.C4N783.valid⟩
  · exact ⟨FiniteK3Cases.C4N784.coeff,FiniteK3Cases.C4N784.valid⟩
  · exact ⟨FiniteK3Cases.C4N785.coeff,FiniteK3Cases.C4N785.valid⟩
  · exact ⟨FiniteK3Cases.C4N786.coeff,FiniteK3Cases.C4N786.valid⟩
  · exact ⟨FiniteK3Cases.C4N787.coeff,FiniteK3Cases.C4N787.valid⟩
  · exact ⟨FiniteK3Cases.C4N788.coeff,FiniteK3Cases.C4N788.valid⟩
  · exact ⟨FiniteK3Cases.C4N789.coeff,FiniteK3Cases.C4N789.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N774To789
