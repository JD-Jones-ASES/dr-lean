import DR.Certificates.FiniteK3Cases.M4N374
import DR.Certificates.FiniteK3Cases.M4N375
import DR.Certificates.FiniteK3Cases.M4N376
import DR.Certificates.FiniteK3Cases.M4N377
import DR.Certificates.FiniteK3Cases.M4N378
import DR.Certificates.FiniteK3Cases.M4N379
import DR.Certificates.FiniteK3Cases.M4N380
import DR.Certificates.FiniteK3Cases.M4N381
import DR.Certificates.FiniteK3Cases.M4N382
import DR.Certificates.FiniteK3Cases.M4N383
import DR.Certificates.FiniteK3Cases.M4N384
import DR.Certificates.FiniteK3Cases.M4N385
import DR.Certificates.FiniteK3Cases.M4N386
import DR.Certificates.FiniteK3Cases.M4N387
import DR.Certificates.FiniteK3Cases.M4N388
import DR.Certificates.FiniteK3Cases.M4N389
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N374To389

theorem exists_valid (n : Nat) (hlo : 374≤n) (hhi : n≤389) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N374.coeff,FiniteK3Cases.C4N374.valid⟩
  · exact ⟨FiniteK3Cases.C4N375.coeff,FiniteK3Cases.C4N375.valid⟩
  · exact ⟨FiniteK3Cases.C4N376.coeff,FiniteK3Cases.C4N376.valid⟩
  · exact ⟨FiniteK3Cases.C4N377.coeff,FiniteK3Cases.C4N377.valid⟩
  · exact ⟨FiniteK3Cases.C4N378.coeff,FiniteK3Cases.C4N378.valid⟩
  · exact ⟨FiniteK3Cases.C4N379.coeff,FiniteK3Cases.C4N379.valid⟩
  · exact ⟨FiniteK3Cases.C4N380.coeff,FiniteK3Cases.C4N380.valid⟩
  · exact ⟨FiniteK3Cases.C4N381.coeff,FiniteK3Cases.C4N381.valid⟩
  · exact ⟨FiniteK3Cases.C4N382.coeff,FiniteK3Cases.C4N382.valid⟩
  · exact ⟨FiniteK3Cases.C4N383.coeff,FiniteK3Cases.C4N383.valid⟩
  · exact ⟨FiniteK3Cases.C4N384.coeff,FiniteK3Cases.C4N384.valid⟩
  · exact ⟨FiniteK3Cases.C4N385.coeff,FiniteK3Cases.C4N385.valid⟩
  · exact ⟨FiniteK3Cases.C4N386.coeff,FiniteK3Cases.C4N386.valid⟩
  · exact ⟨FiniteK3Cases.C4N387.coeff,FiniteK3Cases.C4N387.valid⟩
  · exact ⟨FiniteK3Cases.C4N388.coeff,FiniteK3Cases.C4N388.valid⟩
  · exact ⟨FiniteK3Cases.C4N389.coeff,FiniteK3Cases.C4N389.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N374To389
