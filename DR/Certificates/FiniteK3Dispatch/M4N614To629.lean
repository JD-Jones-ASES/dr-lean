import DR.Certificates.FiniteK3Cases.M4N614
import DR.Certificates.FiniteK3Cases.M4N615
import DR.Certificates.FiniteK3Cases.M4N616
import DR.Certificates.FiniteK3Cases.M4N617
import DR.Certificates.FiniteK3Cases.M4N618
import DR.Certificates.FiniteK3Cases.M4N619
import DR.Certificates.FiniteK3Cases.M4N620
import DR.Certificates.FiniteK3Cases.M4N621
import DR.Certificates.FiniteK3Cases.M4N622
import DR.Certificates.FiniteK3Cases.M4N623
import DR.Certificates.FiniteK3Cases.M4N624
import DR.Certificates.FiniteK3Cases.M4N625
import DR.Certificates.FiniteK3Cases.M4N626
import DR.Certificates.FiniteK3Cases.M4N627
import DR.Certificates.FiniteK3Cases.M4N628
import DR.Certificates.FiniteK3Cases.M4N629
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N614To629

theorem exists_valid (n : Nat) (hlo : 614≤n) (hhi : n≤629) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N614.coeff,FiniteK3Cases.C4N614.valid⟩
  · exact ⟨FiniteK3Cases.C4N615.coeff,FiniteK3Cases.C4N615.valid⟩
  · exact ⟨FiniteK3Cases.C4N616.coeff,FiniteK3Cases.C4N616.valid⟩
  · exact ⟨FiniteK3Cases.C4N617.coeff,FiniteK3Cases.C4N617.valid⟩
  · exact ⟨FiniteK3Cases.C4N618.coeff,FiniteK3Cases.C4N618.valid⟩
  · exact ⟨FiniteK3Cases.C4N619.coeff,FiniteK3Cases.C4N619.valid⟩
  · exact ⟨FiniteK3Cases.C4N620.coeff,FiniteK3Cases.C4N620.valid⟩
  · exact ⟨FiniteK3Cases.C4N621.coeff,FiniteK3Cases.C4N621.valid⟩
  · exact ⟨FiniteK3Cases.C4N622.coeff,FiniteK3Cases.C4N622.valid⟩
  · exact ⟨FiniteK3Cases.C4N623.coeff,FiniteK3Cases.C4N623.valid⟩
  · exact ⟨FiniteK3Cases.C4N624.coeff,FiniteK3Cases.C4N624.valid⟩
  · exact ⟨FiniteK3Cases.C4N625.coeff,FiniteK3Cases.C4N625.valid⟩
  · exact ⟨FiniteK3Cases.C4N626.coeff,FiniteK3Cases.C4N626.valid⟩
  · exact ⟨FiniteK3Cases.C4N627.coeff,FiniteK3Cases.C4N627.valid⟩
  · exact ⟨FiniteK3Cases.C4N628.coeff,FiniteK3Cases.C4N628.valid⟩
  · exact ⟨FiniteK3Cases.C4N629.coeff,FiniteK3Cases.C4N629.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N614To629
