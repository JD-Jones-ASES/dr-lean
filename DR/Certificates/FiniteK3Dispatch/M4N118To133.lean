import DR.Certificates.FiniteK3Cases.M4N118
import DR.Certificates.FiniteK3Cases.M4N119
import DR.Certificates.FiniteK3Cases.M4N120
import DR.Certificates.FiniteK3Cases.M4N121
import DR.Certificates.FiniteK3Cases.M4N122
import DR.Certificates.FiniteK3Cases.M4N123
import DR.Certificates.FiniteK3Cases.M4N124
import DR.Certificates.FiniteK3Cases.M4N125
import DR.Certificates.FiniteK3Cases.M4N126
import DR.Certificates.FiniteK3Cases.M4N127
import DR.Certificates.FiniteK3Cases.M4N128
import DR.Certificates.FiniteK3Cases.M4N129
import DR.Certificates.FiniteK3Cases.M4N130
import DR.Certificates.FiniteK3Cases.M4N131
import DR.Certificates.FiniteK3Cases.M4N132
import DR.Certificates.FiniteK3Cases.M4N133
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N118To133

theorem exists_valid (n : Nat) (hlo : 118≤n) (hhi : n≤133) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N118.coeff,FiniteK3Cases.C4N118.valid⟩
  · exact ⟨FiniteK3Cases.C4N119.coeff,FiniteK3Cases.C4N119.valid⟩
  · exact ⟨FiniteK3Cases.C4N120.coeff,FiniteK3Cases.C4N120.valid⟩
  · exact ⟨FiniteK3Cases.C4N121.coeff,FiniteK3Cases.C4N121.valid⟩
  · exact ⟨FiniteK3Cases.C4N122.coeff,FiniteK3Cases.C4N122.valid⟩
  · exact ⟨FiniteK3Cases.C4N123.coeff,FiniteK3Cases.C4N123.valid⟩
  · exact ⟨FiniteK3Cases.C4N124.coeff,FiniteK3Cases.C4N124.valid⟩
  · exact ⟨FiniteK3Cases.C4N125.coeff,FiniteK3Cases.C4N125.valid⟩
  · exact ⟨FiniteK3Cases.C4N126.coeff,FiniteK3Cases.C4N126.valid⟩
  · exact ⟨FiniteK3Cases.C4N127.coeff,FiniteK3Cases.C4N127.valid⟩
  · exact ⟨FiniteK3Cases.C4N128.coeff,FiniteK3Cases.C4N128.valid⟩
  · exact ⟨FiniteK3Cases.C4N129.coeff,FiniteK3Cases.C4N129.valid⟩
  · exact ⟨FiniteK3Cases.C4N130.coeff,FiniteK3Cases.C4N130.valid⟩
  · exact ⟨FiniteK3Cases.C4N131.coeff,FiniteK3Cases.C4N131.valid⟩
  · exact ⟨FiniteK3Cases.C4N132.coeff,FiniteK3Cases.C4N132.valid⟩
  · exact ⟨FiniteK3Cases.C4N133.coeff,FiniteK3Cases.C4N133.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N118To133
