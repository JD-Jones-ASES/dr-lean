import DR.Certificates.FiniteK3Cases.M4N950
import DR.Certificates.FiniteK3Cases.M4N951
import DR.Certificates.FiniteK3Cases.M4N952
import DR.Certificates.FiniteK3Cases.M4N953
import DR.Certificates.FiniteK3Cases.M4N954
import DR.Certificates.FiniteK3Cases.M4N955
import DR.Certificates.FiniteK3Cases.M4N956
import DR.Certificates.FiniteK3Cases.M4N957
import DR.Certificates.FiniteK3Cases.M4N958
import DR.Certificates.FiniteK3Cases.M4N959
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N950To959

theorem exists_valid (n : Nat) (hlo : 950≤n) (hhi : n≤959) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N950.coeff,FiniteK3Cases.C4N950.valid⟩
  · exact ⟨FiniteK3Cases.C4N951.coeff,FiniteK3Cases.C4N951.valid⟩
  · exact ⟨FiniteK3Cases.C4N952.coeff,FiniteK3Cases.C4N952.valid⟩
  · exact ⟨FiniteK3Cases.C4N953.coeff,FiniteK3Cases.C4N953.valid⟩
  · exact ⟨FiniteK3Cases.C4N954.coeff,FiniteK3Cases.C4N954.valid⟩
  · exact ⟨FiniteK3Cases.C4N955.coeff,FiniteK3Cases.C4N955.valid⟩
  · exact ⟨FiniteK3Cases.C4N956.coeff,FiniteK3Cases.C4N956.valid⟩
  · exact ⟨FiniteK3Cases.C4N957.coeff,FiniteK3Cases.C4N957.valid⟩
  · exact ⟨FiniteK3Cases.C4N958.coeff,FiniteK3Cases.C4N958.valid⟩
  · exact ⟨FiniteK3Cases.C4N959.coeff,FiniteK3Cases.C4N959.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N950To959
