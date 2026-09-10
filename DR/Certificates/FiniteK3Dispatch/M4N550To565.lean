import DR.Certificates.FiniteK3Cases.M4N550
import DR.Certificates.FiniteK3Cases.M4N551
import DR.Certificates.FiniteK3Cases.M4N552
import DR.Certificates.FiniteK3Cases.M4N553
import DR.Certificates.FiniteK3Cases.M4N554
import DR.Certificates.FiniteK3Cases.M4N555
import DR.Certificates.FiniteK3Cases.M4N556
import DR.Certificates.FiniteK3Cases.M4N557
import DR.Certificates.FiniteK3Cases.M4N558
import DR.Certificates.FiniteK3Cases.M4N559
import DR.Certificates.FiniteK3Cases.M4N560
import DR.Certificates.FiniteK3Cases.M4N561
import DR.Certificates.FiniteK3Cases.M4N562
import DR.Certificates.FiniteK3Cases.M4N563
import DR.Certificates.FiniteK3Cases.M4N564
import DR.Certificates.FiniteK3Cases.M4N565
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N550To565

theorem exists_valid (n : Nat) (hlo : 550≤n) (hhi : n≤565) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N550.coeff,FiniteK3Cases.C4N550.valid⟩
  · exact ⟨FiniteK3Cases.C4N551.coeff,FiniteK3Cases.C4N551.valid⟩
  · exact ⟨FiniteK3Cases.C4N552.coeff,FiniteK3Cases.C4N552.valid⟩
  · exact ⟨FiniteK3Cases.C4N553.coeff,FiniteK3Cases.C4N553.valid⟩
  · exact ⟨FiniteK3Cases.C4N554.coeff,FiniteK3Cases.C4N554.valid⟩
  · exact ⟨FiniteK3Cases.C4N555.coeff,FiniteK3Cases.C4N555.valid⟩
  · exact ⟨FiniteK3Cases.C4N556.coeff,FiniteK3Cases.C4N556.valid⟩
  · exact ⟨FiniteK3Cases.C4N557.coeff,FiniteK3Cases.C4N557.valid⟩
  · exact ⟨FiniteK3Cases.C4N558.coeff,FiniteK3Cases.C4N558.valid⟩
  · exact ⟨FiniteK3Cases.C4N559.coeff,FiniteK3Cases.C4N559.valid⟩
  · exact ⟨FiniteK3Cases.C4N560.coeff,FiniteK3Cases.C4N560.valid⟩
  · exact ⟨FiniteK3Cases.C4N561.coeff,FiniteK3Cases.C4N561.valid⟩
  · exact ⟨FiniteK3Cases.C4N562.coeff,FiniteK3Cases.C4N562.valid⟩
  · exact ⟨FiniteK3Cases.C4N563.coeff,FiniteK3Cases.C4N563.valid⟩
  · exact ⟨FiniteK3Cases.C4N564.coeff,FiniteK3Cases.C4N564.valid⟩
  · exact ⟨FiniteK3Cases.C4N565.coeff,FiniteK3Cases.C4N565.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N550To565
