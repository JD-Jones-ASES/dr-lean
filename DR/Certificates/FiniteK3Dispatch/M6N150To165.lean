import DR.Certificates.FiniteK3Cases.M6N150
import DR.Certificates.FiniteK3Cases.M6N151
import DR.Certificates.FiniteK3Cases.M6N152
import DR.Certificates.FiniteK3Cases.M6N153
import DR.Certificates.FiniteK3Cases.M6N154
import DR.Certificates.FiniteK3Cases.M6N155
import DR.Certificates.FiniteK3Cases.M6N156
import DR.Certificates.FiniteK3Cases.M6N157
import DR.Certificates.FiniteK3Cases.M6N158
import DR.Certificates.FiniteK3Cases.M6N159
import DR.Certificates.FiniteK3Cases.M6N160
import DR.Certificates.FiniteK3Cases.M6N161
import DR.Certificates.FiniteK3Cases.M6N162
import DR.Certificates.FiniteK3Cases.M6N163
import DR.Certificates.FiniteK3Cases.M6N164
import DR.Certificates.FiniteK3Cases.M6N165
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N150To165

theorem exists_valid (n : Nat) (hlo : 150≤n) (hhi : n≤165) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N150.coeff,FiniteK3Cases.C6N150.valid⟩
  · exact ⟨FiniteK3Cases.C6N151.coeff,FiniteK3Cases.C6N151.valid⟩
  · exact ⟨FiniteK3Cases.C6N152.coeff,FiniteK3Cases.C6N152.valid⟩
  · exact ⟨FiniteK3Cases.C6N153.coeff,FiniteK3Cases.C6N153.valid⟩
  · exact ⟨FiniteK3Cases.C6N154.coeff,FiniteK3Cases.C6N154.valid⟩
  · exact ⟨FiniteK3Cases.C6N155.coeff,FiniteK3Cases.C6N155.valid⟩
  · exact ⟨FiniteK3Cases.C6N156.coeff,FiniteK3Cases.C6N156.valid⟩
  · exact ⟨FiniteK3Cases.C6N157.coeff,FiniteK3Cases.C6N157.valid⟩
  · exact ⟨FiniteK3Cases.C6N158.coeff,FiniteK3Cases.C6N158.valid⟩
  · exact ⟨FiniteK3Cases.C6N159.coeff,FiniteK3Cases.C6N159.valid⟩
  · exact ⟨FiniteK3Cases.C6N160.coeff,FiniteK3Cases.C6N160.valid⟩
  · exact ⟨FiniteK3Cases.C6N161.coeff,FiniteK3Cases.C6N161.valid⟩
  · exact ⟨FiniteK3Cases.C6N162.coeff,FiniteK3Cases.C6N162.valid⟩
  · exact ⟨FiniteK3Cases.C6N163.coeff,FiniteK3Cases.C6N163.valid⟩
  · exact ⟨FiniteK3Cases.C6N164.coeff,FiniteK3Cases.C6N164.valid⟩
  · exact ⟨FiniteK3Cases.C6N165.coeff,FiniteK3Cases.C6N165.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N150To165
