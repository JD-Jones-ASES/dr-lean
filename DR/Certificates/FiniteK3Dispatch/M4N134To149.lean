import DR.Certificates.FiniteK3Cases.M4N134
import DR.Certificates.FiniteK3Cases.M4N135
import DR.Certificates.FiniteK3Cases.M4N136
import DR.Certificates.FiniteK3Cases.M4N137
import DR.Certificates.FiniteK3Cases.M4N138
import DR.Certificates.FiniteK3Cases.M4N139
import DR.Certificates.FiniteK3Cases.M4N140
import DR.Certificates.FiniteK3Cases.M4N141
import DR.Certificates.FiniteK3Cases.M4N142
import DR.Certificates.FiniteK3Cases.M4N143
import DR.Certificates.FiniteK3Cases.M4N144
import DR.Certificates.FiniteK3Cases.M4N145
import DR.Certificates.FiniteK3Cases.M4N146
import DR.Certificates.FiniteK3Cases.M4N147
import DR.Certificates.FiniteK3Cases.M4N148
import DR.Certificates.FiniteK3Cases.M4N149
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N134To149

theorem exists_valid (n : Nat) (hlo : 134≤n) (hhi : n≤149) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N134.coeff,FiniteK3Cases.C4N134.valid⟩
  · exact ⟨FiniteK3Cases.C4N135.coeff,FiniteK3Cases.C4N135.valid⟩
  · exact ⟨FiniteK3Cases.C4N136.coeff,FiniteK3Cases.C4N136.valid⟩
  · exact ⟨FiniteK3Cases.C4N137.coeff,FiniteK3Cases.C4N137.valid⟩
  · exact ⟨FiniteK3Cases.C4N138.coeff,FiniteK3Cases.C4N138.valid⟩
  · exact ⟨FiniteK3Cases.C4N139.coeff,FiniteK3Cases.C4N139.valid⟩
  · exact ⟨FiniteK3Cases.C4N140.coeff,FiniteK3Cases.C4N140.valid⟩
  · exact ⟨FiniteK3Cases.C4N141.coeff,FiniteK3Cases.C4N141.valid⟩
  · exact ⟨FiniteK3Cases.C4N142.coeff,FiniteK3Cases.C4N142.valid⟩
  · exact ⟨FiniteK3Cases.C4N143.coeff,FiniteK3Cases.C4N143.valid⟩
  · exact ⟨FiniteK3Cases.C4N144.coeff,FiniteK3Cases.C4N144.valid⟩
  · exact ⟨FiniteK3Cases.C4N145.coeff,FiniteK3Cases.C4N145.valid⟩
  · exact ⟨FiniteK3Cases.C4N146.coeff,FiniteK3Cases.C4N146.valid⟩
  · exact ⟨FiniteK3Cases.C4N147.coeff,FiniteK3Cases.C4N147.valid⟩
  · exact ⟨FiniteK3Cases.C4N148.coeff,FiniteK3Cases.C4N148.valid⟩
  · exact ⟨FiniteK3Cases.C4N149.coeff,FiniteK3Cases.C4N149.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N134To149
