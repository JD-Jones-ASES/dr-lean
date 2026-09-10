import DR.Certificates.FiniteK3Cases.M4N486
import DR.Certificates.FiniteK3Cases.M4N487
import DR.Certificates.FiniteK3Cases.M4N488
import DR.Certificates.FiniteK3Cases.M4N489
import DR.Certificates.FiniteK3Cases.M4N490
import DR.Certificates.FiniteK3Cases.M4N491
import DR.Certificates.FiniteK3Cases.M4N492
import DR.Certificates.FiniteK3Cases.M4N493
import DR.Certificates.FiniteK3Cases.M4N494
import DR.Certificates.FiniteK3Cases.M4N495
import DR.Certificates.FiniteK3Cases.M4N496
import DR.Certificates.FiniteK3Cases.M4N497
import DR.Certificates.FiniteK3Cases.M4N498
import DR.Certificates.FiniteK3Cases.M4N499
import DR.Certificates.FiniteK3Cases.M4N500
import DR.Certificates.FiniteK3Cases.M4N501
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N486To501

theorem exists_valid (n : Nat) (hlo : 486≤n) (hhi : n≤501) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N486.coeff,FiniteK3Cases.C4N486.valid⟩
  · exact ⟨FiniteK3Cases.C4N487.coeff,FiniteK3Cases.C4N487.valid⟩
  · exact ⟨FiniteK3Cases.C4N488.coeff,FiniteK3Cases.C4N488.valid⟩
  · exact ⟨FiniteK3Cases.C4N489.coeff,FiniteK3Cases.C4N489.valid⟩
  · exact ⟨FiniteK3Cases.C4N490.coeff,FiniteK3Cases.C4N490.valid⟩
  · exact ⟨FiniteK3Cases.C4N491.coeff,FiniteK3Cases.C4N491.valid⟩
  · exact ⟨FiniteK3Cases.C4N492.coeff,FiniteK3Cases.C4N492.valid⟩
  · exact ⟨FiniteK3Cases.C4N493.coeff,FiniteK3Cases.C4N493.valid⟩
  · exact ⟨FiniteK3Cases.C4N494.coeff,FiniteK3Cases.C4N494.valid⟩
  · exact ⟨FiniteK3Cases.C4N495.coeff,FiniteK3Cases.C4N495.valid⟩
  · exact ⟨FiniteK3Cases.C4N496.coeff,FiniteK3Cases.C4N496.valid⟩
  · exact ⟨FiniteK3Cases.C4N497.coeff,FiniteK3Cases.C4N497.valid⟩
  · exact ⟨FiniteK3Cases.C4N498.coeff,FiniteK3Cases.C4N498.valid⟩
  · exact ⟨FiniteK3Cases.C4N499.coeff,FiniteK3Cases.C4N499.valid⟩
  · exact ⟨FiniteK3Cases.C4N500.coeff,FiniteK3Cases.C4N500.valid⟩
  · exact ⟨FiniteK3Cases.C4N501.coeff,FiniteK3Cases.C4N501.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N486To501
