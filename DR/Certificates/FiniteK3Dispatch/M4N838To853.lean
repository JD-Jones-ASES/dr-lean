import DR.Certificates.FiniteK3Cases.M4N838
import DR.Certificates.FiniteK3Cases.M4N839
import DR.Certificates.FiniteK3Cases.M4N840
import DR.Certificates.FiniteK3Cases.M4N841
import DR.Certificates.FiniteK3Cases.M4N842
import DR.Certificates.FiniteK3Cases.M4N843
import DR.Certificates.FiniteK3Cases.M4N844
import DR.Certificates.FiniteK3Cases.M4N845
import DR.Certificates.FiniteK3Cases.M4N846
import DR.Certificates.FiniteK3Cases.M4N847
import DR.Certificates.FiniteK3Cases.M4N848
import DR.Certificates.FiniteK3Cases.M4N849
import DR.Certificates.FiniteK3Cases.M4N850
import DR.Certificates.FiniteK3Cases.M4N851
import DR.Certificates.FiniteK3Cases.M4N852
import DR.Certificates.FiniteK3Cases.M4N853
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N838To853

theorem exists_valid (n : Nat) (hlo : 838≤n) (hhi : n≤853) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N838.coeff,FiniteK3Cases.C4N838.valid⟩
  · exact ⟨FiniteK3Cases.C4N839.coeff,FiniteK3Cases.C4N839.valid⟩
  · exact ⟨FiniteK3Cases.C4N840.coeff,FiniteK3Cases.C4N840.valid⟩
  · exact ⟨FiniteK3Cases.C4N841.coeff,FiniteK3Cases.C4N841.valid⟩
  · exact ⟨FiniteK3Cases.C4N842.coeff,FiniteK3Cases.C4N842.valid⟩
  · exact ⟨FiniteK3Cases.C4N843.coeff,FiniteK3Cases.C4N843.valid⟩
  · exact ⟨FiniteK3Cases.C4N844.coeff,FiniteK3Cases.C4N844.valid⟩
  · exact ⟨FiniteK3Cases.C4N845.coeff,FiniteK3Cases.C4N845.valid⟩
  · exact ⟨FiniteK3Cases.C4N846.coeff,FiniteK3Cases.C4N846.valid⟩
  · exact ⟨FiniteK3Cases.C4N847.coeff,FiniteK3Cases.C4N847.valid⟩
  · exact ⟨FiniteK3Cases.C4N848.coeff,FiniteK3Cases.C4N848.valid⟩
  · exact ⟨FiniteK3Cases.C4N849.coeff,FiniteK3Cases.C4N849.valid⟩
  · exact ⟨FiniteK3Cases.C4N850.coeff,FiniteK3Cases.C4N850.valid⟩
  · exact ⟨FiniteK3Cases.C4N851.coeff,FiniteK3Cases.C4N851.valid⟩
  · exact ⟨FiniteK3Cases.C4N852.coeff,FiniteK3Cases.C4N852.valid⟩
  · exact ⟨FiniteK3Cases.C4N853.coeff,FiniteK3Cases.C4N853.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N838To853
