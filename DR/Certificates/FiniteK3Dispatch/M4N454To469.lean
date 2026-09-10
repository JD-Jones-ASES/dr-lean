import DR.Certificates.FiniteK3Cases.M4N454
import DR.Certificates.FiniteK3Cases.M4N455
import DR.Certificates.FiniteK3Cases.M4N456
import DR.Certificates.FiniteK3Cases.M4N457
import DR.Certificates.FiniteK3Cases.M4N458
import DR.Certificates.FiniteK3Cases.M4N459
import DR.Certificates.FiniteK3Cases.M4N460
import DR.Certificates.FiniteK3Cases.M4N461
import DR.Certificates.FiniteK3Cases.M4N462
import DR.Certificates.FiniteK3Cases.M4N463
import DR.Certificates.FiniteK3Cases.M4N464
import DR.Certificates.FiniteK3Cases.M4N465
import DR.Certificates.FiniteK3Cases.M4N466
import DR.Certificates.FiniteK3Cases.M4N467
import DR.Certificates.FiniteK3Cases.M4N468
import DR.Certificates.FiniteK3Cases.M4N469
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N454To469

theorem exists_valid (n : Nat) (hlo : 454≤n) (hhi : n≤469) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N454.coeff,FiniteK3Cases.C4N454.valid⟩
  · exact ⟨FiniteK3Cases.C4N455.coeff,FiniteK3Cases.C4N455.valid⟩
  · exact ⟨FiniteK3Cases.C4N456.coeff,FiniteK3Cases.C4N456.valid⟩
  · exact ⟨FiniteK3Cases.C4N457.coeff,FiniteK3Cases.C4N457.valid⟩
  · exact ⟨FiniteK3Cases.C4N458.coeff,FiniteK3Cases.C4N458.valid⟩
  · exact ⟨FiniteK3Cases.C4N459.coeff,FiniteK3Cases.C4N459.valid⟩
  · exact ⟨FiniteK3Cases.C4N460.coeff,FiniteK3Cases.C4N460.valid⟩
  · exact ⟨FiniteK3Cases.C4N461.coeff,FiniteK3Cases.C4N461.valid⟩
  · exact ⟨FiniteK3Cases.C4N462.coeff,FiniteK3Cases.C4N462.valid⟩
  · exact ⟨FiniteK3Cases.C4N463.coeff,FiniteK3Cases.C4N463.valid⟩
  · exact ⟨FiniteK3Cases.C4N464.coeff,FiniteK3Cases.C4N464.valid⟩
  · exact ⟨FiniteK3Cases.C4N465.coeff,FiniteK3Cases.C4N465.valid⟩
  · exact ⟨FiniteK3Cases.C4N466.coeff,FiniteK3Cases.C4N466.valid⟩
  · exact ⟨FiniteK3Cases.C4N467.coeff,FiniteK3Cases.C4N467.valid⟩
  · exact ⟨FiniteK3Cases.C4N468.coeff,FiniteK3Cases.C4N468.valid⟩
  · exact ⟨FiniteK3Cases.C4N469.coeff,FiniteK3Cases.C4N469.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N454To469
