import DR.Certificates.FiniteK3Cases.M4N902
import DR.Certificates.FiniteK3Cases.M4N903
import DR.Certificates.FiniteK3Cases.M4N904
import DR.Certificates.FiniteK3Cases.M4N905
import DR.Certificates.FiniteK3Cases.M4N906
import DR.Certificates.FiniteK3Cases.M4N907
import DR.Certificates.FiniteK3Cases.M4N908
import DR.Certificates.FiniteK3Cases.M4N909
import DR.Certificates.FiniteK3Cases.M4N910
import DR.Certificates.FiniteK3Cases.M4N911
import DR.Certificates.FiniteK3Cases.M4N912
import DR.Certificates.FiniteK3Cases.M4N913
import DR.Certificates.FiniteK3Cases.M4N914
import DR.Certificates.FiniteK3Cases.M4N915
import DR.Certificates.FiniteK3Cases.M4N916
import DR.Certificates.FiniteK3Cases.M4N917
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N902To917

theorem exists_valid (n : Nat) (hlo : 902≤n) (hhi : n≤917) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N902.coeff,FiniteK3Cases.C4N902.valid⟩
  · exact ⟨FiniteK3Cases.C4N903.coeff,FiniteK3Cases.C4N903.valid⟩
  · exact ⟨FiniteK3Cases.C4N904.coeff,FiniteK3Cases.C4N904.valid⟩
  · exact ⟨FiniteK3Cases.C4N905.coeff,FiniteK3Cases.C4N905.valid⟩
  · exact ⟨FiniteK3Cases.C4N906.coeff,FiniteK3Cases.C4N906.valid⟩
  · exact ⟨FiniteK3Cases.C4N907.coeff,FiniteK3Cases.C4N907.valid⟩
  · exact ⟨FiniteK3Cases.C4N908.coeff,FiniteK3Cases.C4N908.valid⟩
  · exact ⟨FiniteK3Cases.C4N909.coeff,FiniteK3Cases.C4N909.valid⟩
  · exact ⟨FiniteK3Cases.C4N910.coeff,FiniteK3Cases.C4N910.valid⟩
  · exact ⟨FiniteK3Cases.C4N911.coeff,FiniteK3Cases.C4N911.valid⟩
  · exact ⟨FiniteK3Cases.C4N912.coeff,FiniteK3Cases.C4N912.valid⟩
  · exact ⟨FiniteK3Cases.C4N913.coeff,FiniteK3Cases.C4N913.valid⟩
  · exact ⟨FiniteK3Cases.C4N914.coeff,FiniteK3Cases.C4N914.valid⟩
  · exact ⟨FiniteK3Cases.C4N915.coeff,FiniteK3Cases.C4N915.valid⟩
  · exact ⟨FiniteK3Cases.C4N916.coeff,FiniteK3Cases.C4N916.valid⟩
  · exact ⟨FiniteK3Cases.C4N917.coeff,FiniteK3Cases.C4N917.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N902To917
