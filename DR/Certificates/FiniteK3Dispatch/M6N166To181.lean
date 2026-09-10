import DR.Certificates.FiniteK3Cases.M6N166
import DR.Certificates.FiniteK3Cases.M6N167
import DR.Certificates.FiniteK3Cases.M6N168
import DR.Certificates.FiniteK3Cases.M6N169
import DR.Certificates.FiniteK3Cases.M6N170
import DR.Certificates.FiniteK3Cases.M6N171
import DR.Certificates.FiniteK3Cases.M6N172
import DR.Certificates.FiniteK3Cases.M6N173
import DR.Certificates.FiniteK3Cases.M6N174
import DR.Certificates.FiniteK3Cases.M6N175
import DR.Certificates.FiniteK3Cases.M6N176
import DR.Certificates.FiniteK3Cases.M6N177
import DR.Certificates.FiniteK3Cases.M6N178
import DR.Certificates.FiniteK3Cases.M6N179
import DR.Certificates.FiniteK3Cases.M6N180
import DR.Certificates.FiniteK3Cases.M6N181
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N166To181

theorem exists_valid (n : Nat) (hlo : 166≤n) (hhi : n≤181) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N166.coeff,FiniteK3Cases.C6N166.valid⟩
  · exact ⟨FiniteK3Cases.C6N167.coeff,FiniteK3Cases.C6N167.valid⟩
  · exact ⟨FiniteK3Cases.C6N168.coeff,FiniteK3Cases.C6N168.valid⟩
  · exact ⟨FiniteK3Cases.C6N169.coeff,FiniteK3Cases.C6N169.valid⟩
  · exact ⟨FiniteK3Cases.C6N170.coeff,FiniteK3Cases.C6N170.valid⟩
  · exact ⟨FiniteK3Cases.C6N171.coeff,FiniteK3Cases.C6N171.valid⟩
  · exact ⟨FiniteK3Cases.C6N172.coeff,FiniteK3Cases.C6N172.valid⟩
  · exact ⟨FiniteK3Cases.C6N173.coeff,FiniteK3Cases.C6N173.valid⟩
  · exact ⟨FiniteK3Cases.C6N174.coeff,FiniteK3Cases.C6N174.valid⟩
  · exact ⟨FiniteK3Cases.C6N175.coeff,FiniteK3Cases.C6N175.valid⟩
  · exact ⟨FiniteK3Cases.C6N176.coeff,FiniteK3Cases.C6N176.valid⟩
  · exact ⟨FiniteK3Cases.C6N177.coeff,FiniteK3Cases.C6N177.valid⟩
  · exact ⟨FiniteK3Cases.C6N178.coeff,FiniteK3Cases.C6N178.valid⟩
  · exact ⟨FiniteK3Cases.C6N179.coeff,FiniteK3Cases.C6N179.valid⟩
  · exact ⟨FiniteK3Cases.C6N180.coeff,FiniteK3Cases.C6N180.valid⟩
  · exact ⟨FiniteK3Cases.C6N181.coeff,FiniteK3Cases.C6N181.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N166To181
