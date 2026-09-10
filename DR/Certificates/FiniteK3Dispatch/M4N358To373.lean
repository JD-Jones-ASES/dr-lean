import DR.Certificates.FiniteK3Cases.M4N358
import DR.Certificates.FiniteK3Cases.M4N359
import DR.Certificates.FiniteK3Cases.M4N360
import DR.Certificates.FiniteK3Cases.M4N361
import DR.Certificates.FiniteK3Cases.M4N362
import DR.Certificates.FiniteK3Cases.M4N363
import DR.Certificates.FiniteK3Cases.M4N364
import DR.Certificates.FiniteK3Cases.M4N365
import DR.Certificates.FiniteK3Cases.M4N366
import DR.Certificates.FiniteK3Cases.M4N367
import DR.Certificates.FiniteK3Cases.M4N368
import DR.Certificates.FiniteK3Cases.M4N369
import DR.Certificates.FiniteK3Cases.M4N370
import DR.Certificates.FiniteK3Cases.M4N371
import DR.Certificates.FiniteK3Cases.M4N372
import DR.Certificates.FiniteK3Cases.M4N373
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N358To373

theorem exists_valid (n : Nat) (hlo : 358≤n) (hhi : n≤373) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N358.coeff,FiniteK3Cases.C4N358.valid⟩
  · exact ⟨FiniteK3Cases.C4N359.coeff,FiniteK3Cases.C4N359.valid⟩
  · exact ⟨FiniteK3Cases.C4N360.coeff,FiniteK3Cases.C4N360.valid⟩
  · exact ⟨FiniteK3Cases.C4N361.coeff,FiniteK3Cases.C4N361.valid⟩
  · exact ⟨FiniteK3Cases.C4N362.coeff,FiniteK3Cases.C4N362.valid⟩
  · exact ⟨FiniteK3Cases.C4N363.coeff,FiniteK3Cases.C4N363.valid⟩
  · exact ⟨FiniteK3Cases.C4N364.coeff,FiniteK3Cases.C4N364.valid⟩
  · exact ⟨FiniteK3Cases.C4N365.coeff,FiniteK3Cases.C4N365.valid⟩
  · exact ⟨FiniteK3Cases.C4N366.coeff,FiniteK3Cases.C4N366.valid⟩
  · exact ⟨FiniteK3Cases.C4N367.coeff,FiniteK3Cases.C4N367.valid⟩
  · exact ⟨FiniteK3Cases.C4N368.coeff,FiniteK3Cases.C4N368.valid⟩
  · exact ⟨FiniteK3Cases.C4N369.coeff,FiniteK3Cases.C4N369.valid⟩
  · exact ⟨FiniteK3Cases.C4N370.coeff,FiniteK3Cases.C4N370.valid⟩
  · exact ⟨FiniteK3Cases.C4N371.coeff,FiniteK3Cases.C4N371.valid⟩
  · exact ⟨FiniteK3Cases.C4N372.coeff,FiniteK3Cases.C4N372.valid⟩
  · exact ⟨FiniteK3Cases.C4N373.coeff,FiniteK3Cases.C4N373.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N358To373
