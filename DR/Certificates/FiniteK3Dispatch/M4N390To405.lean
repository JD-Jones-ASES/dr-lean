import DR.Certificates.FiniteK3Cases.M4N390
import DR.Certificates.FiniteK3Cases.M4N391
import DR.Certificates.FiniteK3Cases.M4N392
import DR.Certificates.FiniteK3Cases.M4N393
import DR.Certificates.FiniteK3Cases.M4N394
import DR.Certificates.FiniteK3Cases.M4N395
import DR.Certificates.FiniteK3Cases.M4N396
import DR.Certificates.FiniteK3Cases.M4N397
import DR.Certificates.FiniteK3Cases.M4N398
import DR.Certificates.FiniteK3Cases.M4N399
import DR.Certificates.FiniteK3Cases.M4N400
import DR.Certificates.FiniteK3Cases.M4N401
import DR.Certificates.FiniteK3Cases.M4N402
import DR.Certificates.FiniteK3Cases.M4N403
import DR.Certificates.FiniteK3Cases.M4N404
import DR.Certificates.FiniteK3Cases.M4N405
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N390To405

theorem exists_valid (n : Nat) (hlo : 390≤n) (hhi : n≤405) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N390.coeff,FiniteK3Cases.C4N390.valid⟩
  · exact ⟨FiniteK3Cases.C4N391.coeff,FiniteK3Cases.C4N391.valid⟩
  · exact ⟨FiniteK3Cases.C4N392.coeff,FiniteK3Cases.C4N392.valid⟩
  · exact ⟨FiniteK3Cases.C4N393.coeff,FiniteK3Cases.C4N393.valid⟩
  · exact ⟨FiniteK3Cases.C4N394.coeff,FiniteK3Cases.C4N394.valid⟩
  · exact ⟨FiniteK3Cases.C4N395.coeff,FiniteK3Cases.C4N395.valid⟩
  · exact ⟨FiniteK3Cases.C4N396.coeff,FiniteK3Cases.C4N396.valid⟩
  · exact ⟨FiniteK3Cases.C4N397.coeff,FiniteK3Cases.C4N397.valid⟩
  · exact ⟨FiniteK3Cases.C4N398.coeff,FiniteK3Cases.C4N398.valid⟩
  · exact ⟨FiniteK3Cases.C4N399.coeff,FiniteK3Cases.C4N399.valid⟩
  · exact ⟨FiniteK3Cases.C4N400.coeff,FiniteK3Cases.C4N400.valid⟩
  · exact ⟨FiniteK3Cases.C4N401.coeff,FiniteK3Cases.C4N401.valid⟩
  · exact ⟨FiniteK3Cases.C4N402.coeff,FiniteK3Cases.C4N402.valid⟩
  · exact ⟨FiniteK3Cases.C4N403.coeff,FiniteK3Cases.C4N403.valid⟩
  · exact ⟨FiniteK3Cases.C4N404.coeff,FiniteK3Cases.C4N404.valid⟩
  · exact ⟨FiniteK3Cases.C4N405.coeff,FiniteK3Cases.C4N405.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N390To405
