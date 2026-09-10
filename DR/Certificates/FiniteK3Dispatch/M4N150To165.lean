import DR.Certificates.FiniteK3Cases.M4N150
import DR.Certificates.FiniteK3Cases.M4N151
import DR.Certificates.FiniteK3Cases.M4N152
import DR.Certificates.FiniteK3Cases.M4N153
import DR.Certificates.FiniteK3Cases.M4N154
import DR.Certificates.FiniteK3Cases.M4N155
import DR.Certificates.FiniteK3Cases.M4N156
import DR.Certificates.FiniteK3Cases.M4N157
import DR.Certificates.FiniteK3Cases.M4N158
import DR.Certificates.FiniteK3Cases.M4N159
import DR.Certificates.FiniteK3Cases.M4N160
import DR.Certificates.FiniteK3Cases.M4N161
import DR.Certificates.FiniteK3Cases.M4N162
import DR.Certificates.FiniteK3Cases.M4N163
import DR.Certificates.FiniteK3Cases.M4N164
import DR.Certificates.FiniteK3Cases.M4N165
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N150To165

theorem exists_valid (n : Nat) (hlo : 150≤n) (hhi : n≤165) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N150.coeff,FiniteK3Cases.C4N150.valid⟩
  · exact ⟨FiniteK3Cases.C4N151.coeff,FiniteK3Cases.C4N151.valid⟩
  · exact ⟨FiniteK3Cases.C4N152.coeff,FiniteK3Cases.C4N152.valid⟩
  · exact ⟨FiniteK3Cases.C4N153.coeff,FiniteK3Cases.C4N153.valid⟩
  · exact ⟨FiniteK3Cases.C4N154.coeff,FiniteK3Cases.C4N154.valid⟩
  · exact ⟨FiniteK3Cases.C4N155.coeff,FiniteK3Cases.C4N155.valid⟩
  · exact ⟨FiniteK3Cases.C4N156.coeff,FiniteK3Cases.C4N156.valid⟩
  · exact ⟨FiniteK3Cases.C4N157.coeff,FiniteK3Cases.C4N157.valid⟩
  · exact ⟨FiniteK3Cases.C4N158.coeff,FiniteK3Cases.C4N158.valid⟩
  · exact ⟨FiniteK3Cases.C4N159.coeff,FiniteK3Cases.C4N159.valid⟩
  · exact ⟨FiniteK3Cases.C4N160.coeff,FiniteK3Cases.C4N160.valid⟩
  · exact ⟨FiniteK3Cases.C4N161.coeff,FiniteK3Cases.C4N161.valid⟩
  · exact ⟨FiniteK3Cases.C4N162.coeff,FiniteK3Cases.C4N162.valid⟩
  · exact ⟨FiniteK3Cases.C4N163.coeff,FiniteK3Cases.C4N163.valid⟩
  · exact ⟨FiniteK3Cases.C4N164.coeff,FiniteK3Cases.C4N164.valid⟩
  · exact ⟨FiniteK3Cases.C4N165.coeff,FiniteK3Cases.C4N165.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N150To165
