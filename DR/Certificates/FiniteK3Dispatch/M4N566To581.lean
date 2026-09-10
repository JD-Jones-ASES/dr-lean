import DR.Certificates.FiniteK3Cases.M4N566
import DR.Certificates.FiniteK3Cases.M4N567
import DR.Certificates.FiniteK3Cases.M4N568
import DR.Certificates.FiniteK3Cases.M4N569
import DR.Certificates.FiniteK3Cases.M4N570
import DR.Certificates.FiniteK3Cases.M4N571
import DR.Certificates.FiniteK3Cases.M4N572
import DR.Certificates.FiniteK3Cases.M4N573
import DR.Certificates.FiniteK3Cases.M4N574
import DR.Certificates.FiniteK3Cases.M4N575
import DR.Certificates.FiniteK3Cases.M4N576
import DR.Certificates.FiniteK3Cases.M4N577
import DR.Certificates.FiniteK3Cases.M4N578
import DR.Certificates.FiniteK3Cases.M4N579
import DR.Certificates.FiniteK3Cases.M4N580
import DR.Certificates.FiniteK3Cases.M4N581
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N566To581

theorem exists_valid (n : Nat) (hlo : 566≤n) (hhi : n≤581) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N566.coeff,FiniteK3Cases.C4N566.valid⟩
  · exact ⟨FiniteK3Cases.C4N567.coeff,FiniteK3Cases.C4N567.valid⟩
  · exact ⟨FiniteK3Cases.C4N568.coeff,FiniteK3Cases.C4N568.valid⟩
  · exact ⟨FiniteK3Cases.C4N569.coeff,FiniteK3Cases.C4N569.valid⟩
  · exact ⟨FiniteK3Cases.C4N570.coeff,FiniteK3Cases.C4N570.valid⟩
  · exact ⟨FiniteK3Cases.C4N571.coeff,FiniteK3Cases.C4N571.valid⟩
  · exact ⟨FiniteK3Cases.C4N572.coeff,FiniteK3Cases.C4N572.valid⟩
  · exact ⟨FiniteK3Cases.C4N573.coeff,FiniteK3Cases.C4N573.valid⟩
  · exact ⟨FiniteK3Cases.C4N574.coeff,FiniteK3Cases.C4N574.valid⟩
  · exact ⟨FiniteK3Cases.C4N575.coeff,FiniteK3Cases.C4N575.valid⟩
  · exact ⟨FiniteK3Cases.C4N576.coeff,FiniteK3Cases.C4N576.valid⟩
  · exact ⟨FiniteK3Cases.C4N577.coeff,FiniteK3Cases.C4N577.valid⟩
  · exact ⟨FiniteK3Cases.C4N578.coeff,FiniteK3Cases.C4N578.valid⟩
  · exact ⟨FiniteK3Cases.C4N579.coeff,FiniteK3Cases.C4N579.valid⟩
  · exact ⟨FiniteK3Cases.C4N580.coeff,FiniteK3Cases.C4N580.valid⟩
  · exact ⟨FiniteK3Cases.C4N581.coeff,FiniteK3Cases.C4N581.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N566To581
