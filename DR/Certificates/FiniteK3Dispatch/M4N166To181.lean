import DR.Certificates.FiniteK3Cases.M4N166
import DR.Certificates.FiniteK3Cases.M4N167
import DR.Certificates.FiniteK3Cases.M4N168
import DR.Certificates.FiniteK3Cases.M4N169
import DR.Certificates.FiniteK3Cases.M4N170
import DR.Certificates.FiniteK3Cases.M4N171
import DR.Certificates.FiniteK3Cases.M4N172
import DR.Certificates.FiniteK3Cases.M4N173
import DR.Certificates.FiniteK3Cases.M4N174
import DR.Certificates.FiniteK3Cases.M4N175
import DR.Certificates.FiniteK3Cases.M4N176
import DR.Certificates.FiniteK3Cases.M4N177
import DR.Certificates.FiniteK3Cases.M4N178
import DR.Certificates.FiniteK3Cases.M4N179
import DR.Certificates.FiniteK3Cases.M4N180
import DR.Certificates.FiniteK3Cases.M4N181
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N166To181

theorem exists_valid (n : Nat) (hlo : 166≤n) (hhi : n≤181) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N166.coeff,FiniteK3Cases.C4N166.valid⟩
  · exact ⟨FiniteK3Cases.C4N167.coeff,FiniteK3Cases.C4N167.valid⟩
  · exact ⟨FiniteK3Cases.C4N168.coeff,FiniteK3Cases.C4N168.valid⟩
  · exact ⟨FiniteK3Cases.C4N169.coeff,FiniteK3Cases.C4N169.valid⟩
  · exact ⟨FiniteK3Cases.C4N170.coeff,FiniteK3Cases.C4N170.valid⟩
  · exact ⟨FiniteK3Cases.C4N171.coeff,FiniteK3Cases.C4N171.valid⟩
  · exact ⟨FiniteK3Cases.C4N172.coeff,FiniteK3Cases.C4N172.valid⟩
  · exact ⟨FiniteK3Cases.C4N173.coeff,FiniteK3Cases.C4N173.valid⟩
  · exact ⟨FiniteK3Cases.C4N174.coeff,FiniteK3Cases.C4N174.valid⟩
  · exact ⟨FiniteK3Cases.C4N175.coeff,FiniteK3Cases.C4N175.valid⟩
  · exact ⟨FiniteK3Cases.C4N176.coeff,FiniteK3Cases.C4N176.valid⟩
  · exact ⟨FiniteK3Cases.C4N177.coeff,FiniteK3Cases.C4N177.valid⟩
  · exact ⟨FiniteK3Cases.C4N178.coeff,FiniteK3Cases.C4N178.valid⟩
  · exact ⟨FiniteK3Cases.C4N179.coeff,FiniteK3Cases.C4N179.valid⟩
  · exact ⟨FiniteK3Cases.C4N180.coeff,FiniteK3Cases.C4N180.valid⟩
  · exact ⟨FiniteK3Cases.C4N181.coeff,FiniteK3Cases.C4N181.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N166To181
