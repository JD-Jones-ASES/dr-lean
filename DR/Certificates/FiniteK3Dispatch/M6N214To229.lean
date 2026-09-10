import DR.Certificates.FiniteK3Cases.M6N214
import DR.Certificates.FiniteK3Cases.M6N215
import DR.Certificates.FiniteK3Cases.M6N216
import DR.Certificates.FiniteK3Cases.M6N217
import DR.Certificates.FiniteK3Cases.M6N218
import DR.Certificates.FiniteK3Cases.M6N219
import DR.Certificates.FiniteK3Cases.M6N220
import DR.Certificates.FiniteK3Cases.M6N221
import DR.Certificates.FiniteK3Cases.M6N222
import DR.Certificates.FiniteK3Cases.M6N223
import DR.Certificates.FiniteK3Cases.M6N224
import DR.Certificates.FiniteK3Cases.M6N225
import DR.Certificates.FiniteK3Cases.M6N226
import DR.Certificates.FiniteK3Cases.M6N227
import DR.Certificates.FiniteK3Cases.M6N228
import DR.Certificates.FiniteK3Cases.M6N229
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N214To229

theorem exists_valid (n : Nat) (hlo : 214≤n) (hhi : n≤229) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N214.coeff,FiniteK3Cases.C6N214.valid⟩
  · exact ⟨FiniteK3Cases.C6N215.coeff,FiniteK3Cases.C6N215.valid⟩
  · exact ⟨FiniteK3Cases.C6N216.coeff,FiniteK3Cases.C6N216.valid⟩
  · exact ⟨FiniteK3Cases.C6N217.coeff,FiniteK3Cases.C6N217.valid⟩
  · exact ⟨FiniteK3Cases.C6N218.coeff,FiniteK3Cases.C6N218.valid⟩
  · exact ⟨FiniteK3Cases.C6N219.coeff,FiniteK3Cases.C6N219.valid⟩
  · exact ⟨FiniteK3Cases.C6N220.coeff,FiniteK3Cases.C6N220.valid⟩
  · exact ⟨FiniteK3Cases.C6N221.coeff,FiniteK3Cases.C6N221.valid⟩
  · exact ⟨FiniteK3Cases.C6N222.coeff,FiniteK3Cases.C6N222.valid⟩
  · exact ⟨FiniteK3Cases.C6N223.coeff,FiniteK3Cases.C6N223.valid⟩
  · exact ⟨FiniteK3Cases.C6N224.coeff,FiniteK3Cases.C6N224.valid⟩
  · exact ⟨FiniteK3Cases.C6N225.coeff,FiniteK3Cases.C6N225.valid⟩
  · exact ⟨FiniteK3Cases.C6N226.coeff,FiniteK3Cases.C6N226.valid⟩
  · exact ⟨FiniteK3Cases.C6N227.coeff,FiniteK3Cases.C6N227.valid⟩
  · exact ⟨FiniteK3Cases.C6N228.coeff,FiniteK3Cases.C6N228.valid⟩
  · exact ⟨FiniteK3Cases.C6N229.coeff,FiniteK3Cases.C6N229.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N214To229
