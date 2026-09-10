import DR.Certificates.FiniteK3Cases.M6N118
import DR.Certificates.FiniteK3Cases.M6N119
import DR.Certificates.FiniteK3Cases.M6N120
import DR.Certificates.FiniteK3Cases.M6N121
import DR.Certificates.FiniteK3Cases.M6N122
import DR.Certificates.FiniteK3Cases.M6N123
import DR.Certificates.FiniteK3Cases.M6N124
import DR.Certificates.FiniteK3Cases.M6N125
import DR.Certificates.FiniteK3Cases.M6N126
import DR.Certificates.FiniteK3Cases.M6N127
import DR.Certificates.FiniteK3Cases.M6N128
import DR.Certificates.FiniteK3Cases.M6N129
import DR.Certificates.FiniteK3Cases.M6N130
import DR.Certificates.FiniteK3Cases.M6N131
import DR.Certificates.FiniteK3Cases.M6N132
import DR.Certificates.FiniteK3Cases.M6N133
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N118To133

theorem exists_valid (n : Nat) (hlo : 118≤n) (hhi : n≤133) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N118.coeff,FiniteK3Cases.C6N118.valid⟩
  · exact ⟨FiniteK3Cases.C6N119.coeff,FiniteK3Cases.C6N119.valid⟩
  · exact ⟨FiniteK3Cases.C6N120.coeff,FiniteK3Cases.C6N120.valid⟩
  · exact ⟨FiniteK3Cases.C6N121.coeff,FiniteK3Cases.C6N121.valid⟩
  · exact ⟨FiniteK3Cases.C6N122.coeff,FiniteK3Cases.C6N122.valid⟩
  · exact ⟨FiniteK3Cases.C6N123.coeff,FiniteK3Cases.C6N123.valid⟩
  · exact ⟨FiniteK3Cases.C6N124.coeff,FiniteK3Cases.C6N124.valid⟩
  · exact ⟨FiniteK3Cases.C6N125.coeff,FiniteK3Cases.C6N125.valid⟩
  · exact ⟨FiniteK3Cases.C6N126.coeff,FiniteK3Cases.C6N126.valid⟩
  · exact ⟨FiniteK3Cases.C6N127.coeff,FiniteK3Cases.C6N127.valid⟩
  · exact ⟨FiniteK3Cases.C6N128.coeff,FiniteK3Cases.C6N128.valid⟩
  · exact ⟨FiniteK3Cases.C6N129.coeff,FiniteK3Cases.C6N129.valid⟩
  · exact ⟨FiniteK3Cases.C6N130.coeff,FiniteK3Cases.C6N130.valid⟩
  · exact ⟨FiniteK3Cases.C6N131.coeff,FiniteK3Cases.C6N131.valid⟩
  · exact ⟨FiniteK3Cases.C6N132.coeff,FiniteK3Cases.C6N132.valid⟩
  · exact ⟨FiniteK3Cases.C6N133.coeff,FiniteK3Cases.C6N133.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N118To133
