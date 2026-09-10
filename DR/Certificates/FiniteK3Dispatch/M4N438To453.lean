import DR.Certificates.FiniteK3Cases.M4N438
import DR.Certificates.FiniteK3Cases.M4N439
import DR.Certificates.FiniteK3Cases.M4N440
import DR.Certificates.FiniteK3Cases.M4N441
import DR.Certificates.FiniteK3Cases.M4N442
import DR.Certificates.FiniteK3Cases.M4N443
import DR.Certificates.FiniteK3Cases.M4N444
import DR.Certificates.FiniteK3Cases.M4N445
import DR.Certificates.FiniteK3Cases.M4N446
import DR.Certificates.FiniteK3Cases.M4N447
import DR.Certificates.FiniteK3Cases.M4N448
import DR.Certificates.FiniteK3Cases.M4N449
import DR.Certificates.FiniteK3Cases.M4N450
import DR.Certificates.FiniteK3Cases.M4N451
import DR.Certificates.FiniteK3Cases.M4N452
import DR.Certificates.FiniteK3Cases.M4N453
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N438To453

theorem exists_valid (n : Nat) (hlo : 438≤n) (hhi : n≤453) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N438.coeff,FiniteK3Cases.C4N438.valid⟩
  · exact ⟨FiniteK3Cases.C4N439.coeff,FiniteK3Cases.C4N439.valid⟩
  · exact ⟨FiniteK3Cases.C4N440.coeff,FiniteK3Cases.C4N440.valid⟩
  · exact ⟨FiniteK3Cases.C4N441.coeff,FiniteK3Cases.C4N441.valid⟩
  · exact ⟨FiniteK3Cases.C4N442.coeff,FiniteK3Cases.C4N442.valid⟩
  · exact ⟨FiniteK3Cases.C4N443.coeff,FiniteK3Cases.C4N443.valid⟩
  · exact ⟨FiniteK3Cases.C4N444.coeff,FiniteK3Cases.C4N444.valid⟩
  · exact ⟨FiniteK3Cases.C4N445.coeff,FiniteK3Cases.C4N445.valid⟩
  · exact ⟨FiniteK3Cases.C4N446.coeff,FiniteK3Cases.C4N446.valid⟩
  · exact ⟨FiniteK3Cases.C4N447.coeff,FiniteK3Cases.C4N447.valid⟩
  · exact ⟨FiniteK3Cases.C4N448.coeff,FiniteK3Cases.C4N448.valid⟩
  · exact ⟨FiniteK3Cases.C4N449.coeff,FiniteK3Cases.C4N449.valid⟩
  · exact ⟨FiniteK3Cases.C4N450.coeff,FiniteK3Cases.C4N450.valid⟩
  · exact ⟨FiniteK3Cases.C4N451.coeff,FiniteK3Cases.C4N451.valid⟩
  · exact ⟨FiniteK3Cases.C4N452.coeff,FiniteK3Cases.C4N452.valid⟩
  · exact ⟨FiniteK3Cases.C4N453.coeff,FiniteK3Cases.C4N453.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N438To453
