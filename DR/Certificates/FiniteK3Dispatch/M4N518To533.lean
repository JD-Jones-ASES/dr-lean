import DR.Certificates.FiniteK3Cases.M4N518
import DR.Certificates.FiniteK3Cases.M4N519
import DR.Certificates.FiniteK3Cases.M4N520
import DR.Certificates.FiniteK3Cases.M4N521
import DR.Certificates.FiniteK3Cases.M4N522
import DR.Certificates.FiniteK3Cases.M4N523
import DR.Certificates.FiniteK3Cases.M4N524
import DR.Certificates.FiniteK3Cases.M4N525
import DR.Certificates.FiniteK3Cases.M4N526
import DR.Certificates.FiniteK3Cases.M4N527
import DR.Certificates.FiniteK3Cases.M4N528
import DR.Certificates.FiniteK3Cases.M4N529
import DR.Certificates.FiniteK3Cases.M4N530
import DR.Certificates.FiniteK3Cases.M4N531
import DR.Certificates.FiniteK3Cases.M4N532
import DR.Certificates.FiniteK3Cases.M4N533
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N518To533

theorem exists_valid (n : Nat) (hlo : 518≤n) (hhi : n≤533) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N518.coeff,FiniteK3Cases.C4N518.valid⟩
  · exact ⟨FiniteK3Cases.C4N519.coeff,FiniteK3Cases.C4N519.valid⟩
  · exact ⟨FiniteK3Cases.C4N520.coeff,FiniteK3Cases.C4N520.valid⟩
  · exact ⟨FiniteK3Cases.C4N521.coeff,FiniteK3Cases.C4N521.valid⟩
  · exact ⟨FiniteK3Cases.C4N522.coeff,FiniteK3Cases.C4N522.valid⟩
  · exact ⟨FiniteK3Cases.C4N523.coeff,FiniteK3Cases.C4N523.valid⟩
  · exact ⟨FiniteK3Cases.C4N524.coeff,FiniteK3Cases.C4N524.valid⟩
  · exact ⟨FiniteK3Cases.C4N525.coeff,FiniteK3Cases.C4N525.valid⟩
  · exact ⟨FiniteK3Cases.C4N526.coeff,FiniteK3Cases.C4N526.valid⟩
  · exact ⟨FiniteK3Cases.C4N527.coeff,FiniteK3Cases.C4N527.valid⟩
  · exact ⟨FiniteK3Cases.C4N528.coeff,FiniteK3Cases.C4N528.valid⟩
  · exact ⟨FiniteK3Cases.C4N529.coeff,FiniteK3Cases.C4N529.valid⟩
  · exact ⟨FiniteK3Cases.C4N530.coeff,FiniteK3Cases.C4N530.valid⟩
  · exact ⟨FiniteK3Cases.C4N531.coeff,FiniteK3Cases.C4N531.valid⟩
  · exact ⟨FiniteK3Cases.C4N532.coeff,FiniteK3Cases.C4N532.valid⟩
  · exact ⟨FiniteK3Cases.C4N533.coeff,FiniteK3Cases.C4N533.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N518To533
