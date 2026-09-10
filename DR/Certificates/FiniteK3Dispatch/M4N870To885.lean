import DR.Certificates.FiniteK3Cases.M4N870
import DR.Certificates.FiniteK3Cases.M4N871
import DR.Certificates.FiniteK3Cases.M4N872
import DR.Certificates.FiniteK3Cases.M4N873
import DR.Certificates.FiniteK3Cases.M4N874
import DR.Certificates.FiniteK3Cases.M4N875
import DR.Certificates.FiniteK3Cases.M4N876
import DR.Certificates.FiniteK3Cases.M4N877
import DR.Certificates.FiniteK3Cases.M4N878
import DR.Certificates.FiniteK3Cases.M4N879
import DR.Certificates.FiniteK3Cases.M4N880
import DR.Certificates.FiniteK3Cases.M4N881
import DR.Certificates.FiniteK3Cases.M4N882
import DR.Certificates.FiniteK3Cases.M4N883
import DR.Certificates.FiniteK3Cases.M4N884
import DR.Certificates.FiniteK3Cases.M4N885
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N870To885

theorem exists_valid (n : Nat) (hlo : 870≤n) (hhi : n≤885) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N870.coeff,FiniteK3Cases.C4N870.valid⟩
  · exact ⟨FiniteK3Cases.C4N871.coeff,FiniteK3Cases.C4N871.valid⟩
  · exact ⟨FiniteK3Cases.C4N872.coeff,FiniteK3Cases.C4N872.valid⟩
  · exact ⟨FiniteK3Cases.C4N873.coeff,FiniteK3Cases.C4N873.valid⟩
  · exact ⟨FiniteK3Cases.C4N874.coeff,FiniteK3Cases.C4N874.valid⟩
  · exact ⟨FiniteK3Cases.C4N875.coeff,FiniteK3Cases.C4N875.valid⟩
  · exact ⟨FiniteK3Cases.C4N876.coeff,FiniteK3Cases.C4N876.valid⟩
  · exact ⟨FiniteK3Cases.C4N877.coeff,FiniteK3Cases.C4N877.valid⟩
  · exact ⟨FiniteK3Cases.C4N878.coeff,FiniteK3Cases.C4N878.valid⟩
  · exact ⟨FiniteK3Cases.C4N879.coeff,FiniteK3Cases.C4N879.valid⟩
  · exact ⟨FiniteK3Cases.C4N880.coeff,FiniteK3Cases.C4N880.valid⟩
  · exact ⟨FiniteK3Cases.C4N881.coeff,FiniteK3Cases.C4N881.valid⟩
  · exact ⟨FiniteK3Cases.C4N882.coeff,FiniteK3Cases.C4N882.valid⟩
  · exact ⟨FiniteK3Cases.C4N883.coeff,FiniteK3Cases.C4N883.valid⟩
  · exact ⟨FiniteK3Cases.C4N884.coeff,FiniteK3Cases.C4N884.valid⟩
  · exact ⟨FiniteK3Cases.C4N885.coeff,FiniteK3Cases.C4N885.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N870To885
