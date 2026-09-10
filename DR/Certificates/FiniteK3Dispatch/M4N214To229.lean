import DR.Certificates.FiniteK3Cases.M4N214
import DR.Certificates.FiniteK3Cases.M4N215
import DR.Certificates.FiniteK3Cases.M4N216
import DR.Certificates.FiniteK3Cases.M4N217
import DR.Certificates.FiniteK3Cases.M4N218
import DR.Certificates.FiniteK3Cases.M4N219
import DR.Certificates.FiniteK3Cases.M4N220
import DR.Certificates.FiniteK3Cases.M4N221
import DR.Certificates.FiniteK3Cases.M4N222
import DR.Certificates.FiniteK3Cases.M4N223
import DR.Certificates.FiniteK3Cases.M4N224
import DR.Certificates.FiniteK3Cases.M4N225
import DR.Certificates.FiniteK3Cases.M4N226
import DR.Certificates.FiniteK3Cases.M4N227
import DR.Certificates.FiniteK3Cases.M4N228
import DR.Certificates.FiniteK3Cases.M4N229
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N214To229

theorem exists_valid (n : Nat) (hlo : 214≤n) (hhi : n≤229) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N214.coeff,FiniteK3Cases.C4N214.valid⟩
  · exact ⟨FiniteK3Cases.C4N215.coeff,FiniteK3Cases.C4N215.valid⟩
  · exact ⟨FiniteK3Cases.C4N216.coeff,FiniteK3Cases.C4N216.valid⟩
  · exact ⟨FiniteK3Cases.C4N217.coeff,FiniteK3Cases.C4N217.valid⟩
  · exact ⟨FiniteK3Cases.C4N218.coeff,FiniteK3Cases.C4N218.valid⟩
  · exact ⟨FiniteK3Cases.C4N219.coeff,FiniteK3Cases.C4N219.valid⟩
  · exact ⟨FiniteK3Cases.C4N220.coeff,FiniteK3Cases.C4N220.valid⟩
  · exact ⟨FiniteK3Cases.C4N221.coeff,FiniteK3Cases.C4N221.valid⟩
  · exact ⟨FiniteK3Cases.C4N222.coeff,FiniteK3Cases.C4N222.valid⟩
  · exact ⟨FiniteK3Cases.C4N223.coeff,FiniteK3Cases.C4N223.valid⟩
  · exact ⟨FiniteK3Cases.C4N224.coeff,FiniteK3Cases.C4N224.valid⟩
  · exact ⟨FiniteK3Cases.C4N225.coeff,FiniteK3Cases.C4N225.valid⟩
  · exact ⟨FiniteK3Cases.C4N226.coeff,FiniteK3Cases.C4N226.valid⟩
  · exact ⟨FiniteK3Cases.C4N227.coeff,FiniteK3Cases.C4N227.valid⟩
  · exact ⟨FiniteK3Cases.C4N228.coeff,FiniteK3Cases.C4N228.valid⟩
  · exact ⟨FiniteK3Cases.C4N229.coeff,FiniteK3Cases.C4N229.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N214To229
