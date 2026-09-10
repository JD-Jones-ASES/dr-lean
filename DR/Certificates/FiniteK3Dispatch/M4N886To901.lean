import DR.Certificates.FiniteK3Cases.M4N886
import DR.Certificates.FiniteK3Cases.M4N887
import DR.Certificates.FiniteK3Cases.M4N888
import DR.Certificates.FiniteK3Cases.M4N889
import DR.Certificates.FiniteK3Cases.M4N890
import DR.Certificates.FiniteK3Cases.M4N891
import DR.Certificates.FiniteK3Cases.M4N892
import DR.Certificates.FiniteK3Cases.M4N893
import DR.Certificates.FiniteK3Cases.M4N894
import DR.Certificates.FiniteK3Cases.M4N895
import DR.Certificates.FiniteK3Cases.M4N896
import DR.Certificates.FiniteK3Cases.M4N897
import DR.Certificates.FiniteK3Cases.M4N898
import DR.Certificates.FiniteK3Cases.M4N899
import DR.Certificates.FiniteK3Cases.M4N900
import DR.Certificates.FiniteK3Cases.M4N901
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N886To901

theorem exists_valid (n : Nat) (hlo : 886≤n) (hhi : n≤901) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N886.coeff,FiniteK3Cases.C4N886.valid⟩
  · exact ⟨FiniteK3Cases.C4N887.coeff,FiniteK3Cases.C4N887.valid⟩
  · exact ⟨FiniteK3Cases.C4N888.coeff,FiniteK3Cases.C4N888.valid⟩
  · exact ⟨FiniteK3Cases.C4N889.coeff,FiniteK3Cases.C4N889.valid⟩
  · exact ⟨FiniteK3Cases.C4N890.coeff,FiniteK3Cases.C4N890.valid⟩
  · exact ⟨FiniteK3Cases.C4N891.coeff,FiniteK3Cases.C4N891.valid⟩
  · exact ⟨FiniteK3Cases.C4N892.coeff,FiniteK3Cases.C4N892.valid⟩
  · exact ⟨FiniteK3Cases.C4N893.coeff,FiniteK3Cases.C4N893.valid⟩
  · exact ⟨FiniteK3Cases.C4N894.coeff,FiniteK3Cases.C4N894.valid⟩
  · exact ⟨FiniteK3Cases.C4N895.coeff,FiniteK3Cases.C4N895.valid⟩
  · exact ⟨FiniteK3Cases.C4N896.coeff,FiniteK3Cases.C4N896.valid⟩
  · exact ⟨FiniteK3Cases.C4N897.coeff,FiniteK3Cases.C4N897.valid⟩
  · exact ⟨FiniteK3Cases.C4N898.coeff,FiniteK3Cases.C4N898.valid⟩
  · exact ⟨FiniteK3Cases.C4N899.coeff,FiniteK3Cases.C4N899.valid⟩
  · exact ⟨FiniteK3Cases.C4N900.coeff,FiniteK3Cases.C4N900.valid⟩
  · exact ⟨FiniteK3Cases.C4N901.coeff,FiniteK3Cases.C4N901.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N886To901
