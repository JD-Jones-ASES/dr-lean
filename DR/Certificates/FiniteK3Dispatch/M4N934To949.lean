import DR.Certificates.FiniteK3Cases.M4N934
import DR.Certificates.FiniteK3Cases.M4N935
import DR.Certificates.FiniteK3Cases.M4N936
import DR.Certificates.FiniteK3Cases.M4N937
import DR.Certificates.FiniteK3Cases.M4N938
import DR.Certificates.FiniteK3Cases.M4N939
import DR.Certificates.FiniteK3Cases.M4N940
import DR.Certificates.FiniteK3Cases.M4N941
import DR.Certificates.FiniteK3Cases.M4N942
import DR.Certificates.FiniteK3Cases.M4N943
import DR.Certificates.FiniteK3Cases.M4N944
import DR.Certificates.FiniteK3Cases.M4N945
import DR.Certificates.FiniteK3Cases.M4N946
import DR.Certificates.FiniteK3Cases.M4N947
import DR.Certificates.FiniteK3Cases.M4N948
import DR.Certificates.FiniteK3Cases.M4N949
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N934To949

theorem exists_valid (n : Nat) (hlo : 934≤n) (hhi : n≤949) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N934.coeff,FiniteK3Cases.C4N934.valid⟩
  · exact ⟨FiniteK3Cases.C4N935.coeff,FiniteK3Cases.C4N935.valid⟩
  · exact ⟨FiniteK3Cases.C4N936.coeff,FiniteK3Cases.C4N936.valid⟩
  · exact ⟨FiniteK3Cases.C4N937.coeff,FiniteK3Cases.C4N937.valid⟩
  · exact ⟨FiniteK3Cases.C4N938.coeff,FiniteK3Cases.C4N938.valid⟩
  · exact ⟨FiniteK3Cases.C4N939.coeff,FiniteK3Cases.C4N939.valid⟩
  · exact ⟨FiniteK3Cases.C4N940.coeff,FiniteK3Cases.C4N940.valid⟩
  · exact ⟨FiniteK3Cases.C4N941.coeff,FiniteK3Cases.C4N941.valid⟩
  · exact ⟨FiniteK3Cases.C4N942.coeff,FiniteK3Cases.C4N942.valid⟩
  · exact ⟨FiniteK3Cases.C4N943.coeff,FiniteK3Cases.C4N943.valid⟩
  · exact ⟨FiniteK3Cases.C4N944.coeff,FiniteK3Cases.C4N944.valid⟩
  · exact ⟨FiniteK3Cases.C4N945.coeff,FiniteK3Cases.C4N945.valid⟩
  · exact ⟨FiniteK3Cases.C4N946.coeff,FiniteK3Cases.C4N946.valid⟩
  · exact ⟨FiniteK3Cases.C4N947.coeff,FiniteK3Cases.C4N947.valid⟩
  · exact ⟨FiniteK3Cases.C4N948.coeff,FiniteK3Cases.C4N948.valid⟩
  · exact ⟨FiniteK3Cases.C4N949.coeff,FiniteK3Cases.C4N949.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N934To949
