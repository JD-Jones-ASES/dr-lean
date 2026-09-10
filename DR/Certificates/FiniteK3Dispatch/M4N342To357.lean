import DR.Certificates.FiniteK3Cases.M4N342
import DR.Certificates.FiniteK3Cases.M4N343
import DR.Certificates.FiniteK3Cases.M4N344
import DR.Certificates.FiniteK3Cases.M4N345
import DR.Certificates.FiniteK3Cases.M4N346
import DR.Certificates.FiniteK3Cases.M4N347
import DR.Certificates.FiniteK3Cases.M4N348
import DR.Certificates.FiniteK3Cases.M4N349
import DR.Certificates.FiniteK3Cases.M4N350
import DR.Certificates.FiniteK3Cases.M4N351
import DR.Certificates.FiniteK3Cases.M4N352
import DR.Certificates.FiniteK3Cases.M4N353
import DR.Certificates.FiniteK3Cases.M4N354
import DR.Certificates.FiniteK3Cases.M4N355
import DR.Certificates.FiniteK3Cases.M4N356
import DR.Certificates.FiniteK3Cases.M4N357
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N342To357

theorem exists_valid (n : Nat) (hlo : 342≤n) (hhi : n≤357) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N342.coeff,FiniteK3Cases.C4N342.valid⟩
  · exact ⟨FiniteK3Cases.C4N343.coeff,FiniteK3Cases.C4N343.valid⟩
  · exact ⟨FiniteK3Cases.C4N344.coeff,FiniteK3Cases.C4N344.valid⟩
  · exact ⟨FiniteK3Cases.C4N345.coeff,FiniteK3Cases.C4N345.valid⟩
  · exact ⟨FiniteK3Cases.C4N346.coeff,FiniteK3Cases.C4N346.valid⟩
  · exact ⟨FiniteK3Cases.C4N347.coeff,FiniteK3Cases.C4N347.valid⟩
  · exact ⟨FiniteK3Cases.C4N348.coeff,FiniteK3Cases.C4N348.valid⟩
  · exact ⟨FiniteK3Cases.C4N349.coeff,FiniteK3Cases.C4N349.valid⟩
  · exact ⟨FiniteK3Cases.C4N350.coeff,FiniteK3Cases.C4N350.valid⟩
  · exact ⟨FiniteK3Cases.C4N351.coeff,FiniteK3Cases.C4N351.valid⟩
  · exact ⟨FiniteK3Cases.C4N352.coeff,FiniteK3Cases.C4N352.valid⟩
  · exact ⟨FiniteK3Cases.C4N353.coeff,FiniteK3Cases.C4N353.valid⟩
  · exact ⟨FiniteK3Cases.C4N354.coeff,FiniteK3Cases.C4N354.valid⟩
  · exact ⟨FiniteK3Cases.C4N355.coeff,FiniteK3Cases.C4N355.valid⟩
  · exact ⟨FiniteK3Cases.C4N356.coeff,FiniteK3Cases.C4N356.valid⟩
  · exact ⟨FiniteK3Cases.C4N357.coeff,FiniteK3Cases.C4N357.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N342To357
