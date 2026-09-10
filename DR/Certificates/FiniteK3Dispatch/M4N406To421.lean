import DR.Certificates.FiniteK3Cases.M4N406
import DR.Certificates.FiniteK3Cases.M4N407
import DR.Certificates.FiniteK3Cases.M4N408
import DR.Certificates.FiniteK3Cases.M4N409
import DR.Certificates.FiniteK3Cases.M4N410
import DR.Certificates.FiniteK3Cases.M4N411
import DR.Certificates.FiniteK3Cases.M4N412
import DR.Certificates.FiniteK3Cases.M4N413
import DR.Certificates.FiniteK3Cases.M4N414
import DR.Certificates.FiniteK3Cases.M4N415
import DR.Certificates.FiniteK3Cases.M4N416
import DR.Certificates.FiniteK3Cases.M4N417
import DR.Certificates.FiniteK3Cases.M4N418
import DR.Certificates.FiniteK3Cases.M4N419
import DR.Certificates.FiniteK3Cases.M4N420
import DR.Certificates.FiniteK3Cases.M4N421
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N406To421

theorem exists_valid (n : Nat) (hlo : 406≤n) (hhi : n≤421) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N406.coeff,FiniteK3Cases.C4N406.valid⟩
  · exact ⟨FiniteK3Cases.C4N407.coeff,FiniteK3Cases.C4N407.valid⟩
  · exact ⟨FiniteK3Cases.C4N408.coeff,FiniteK3Cases.C4N408.valid⟩
  · exact ⟨FiniteK3Cases.C4N409.coeff,FiniteK3Cases.C4N409.valid⟩
  · exact ⟨FiniteK3Cases.C4N410.coeff,FiniteK3Cases.C4N410.valid⟩
  · exact ⟨FiniteK3Cases.C4N411.coeff,FiniteK3Cases.C4N411.valid⟩
  · exact ⟨FiniteK3Cases.C4N412.coeff,FiniteK3Cases.C4N412.valid⟩
  · exact ⟨FiniteK3Cases.C4N413.coeff,FiniteK3Cases.C4N413.valid⟩
  · exact ⟨FiniteK3Cases.C4N414.coeff,FiniteK3Cases.C4N414.valid⟩
  · exact ⟨FiniteK3Cases.C4N415.coeff,FiniteK3Cases.C4N415.valid⟩
  · exact ⟨FiniteK3Cases.C4N416.coeff,FiniteK3Cases.C4N416.valid⟩
  · exact ⟨FiniteK3Cases.C4N417.coeff,FiniteK3Cases.C4N417.valid⟩
  · exact ⟨FiniteK3Cases.C4N418.coeff,FiniteK3Cases.C4N418.valid⟩
  · exact ⟨FiniteK3Cases.C4N419.coeff,FiniteK3Cases.C4N419.valid⟩
  · exact ⟨FiniteK3Cases.C4N420.coeff,FiniteK3Cases.C4N420.valid⟩
  · exact ⟨FiniteK3Cases.C4N421.coeff,FiniteK3Cases.C4N421.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N406To421
