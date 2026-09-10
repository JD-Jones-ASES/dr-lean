import DR.Certificates.FiniteK3Cases.M6N134
import DR.Certificates.FiniteK3Cases.M6N135
import DR.Certificates.FiniteK3Cases.M6N136
import DR.Certificates.FiniteK3Cases.M6N137
import DR.Certificates.FiniteK3Cases.M6N138
import DR.Certificates.FiniteK3Cases.M6N139
import DR.Certificates.FiniteK3Cases.M6N140
import DR.Certificates.FiniteK3Cases.M6N141
import DR.Certificates.FiniteK3Cases.M6N142
import DR.Certificates.FiniteK3Cases.M6N143
import DR.Certificates.FiniteK3Cases.M6N144
import DR.Certificates.FiniteK3Cases.M6N145
import DR.Certificates.FiniteK3Cases.M6N146
import DR.Certificates.FiniteK3Cases.M6N147
import DR.Certificates.FiniteK3Cases.M6N148
import DR.Certificates.FiniteK3Cases.M6N149
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N134To149

theorem exists_valid (n : Nat) (hlo : 134≤n) (hhi : n≤149) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N134.coeff,FiniteK3Cases.C6N134.valid⟩
  · exact ⟨FiniteK3Cases.C6N135.coeff,FiniteK3Cases.C6N135.valid⟩
  · exact ⟨FiniteK3Cases.C6N136.coeff,FiniteK3Cases.C6N136.valid⟩
  · exact ⟨FiniteK3Cases.C6N137.coeff,FiniteK3Cases.C6N137.valid⟩
  · exact ⟨FiniteK3Cases.C6N138.coeff,FiniteK3Cases.C6N138.valid⟩
  · exact ⟨FiniteK3Cases.C6N139.coeff,FiniteK3Cases.C6N139.valid⟩
  · exact ⟨FiniteK3Cases.C6N140.coeff,FiniteK3Cases.C6N140.valid⟩
  · exact ⟨FiniteK3Cases.C6N141.coeff,FiniteK3Cases.C6N141.valid⟩
  · exact ⟨FiniteK3Cases.C6N142.coeff,FiniteK3Cases.C6N142.valid⟩
  · exact ⟨FiniteK3Cases.C6N143.coeff,FiniteK3Cases.C6N143.valid⟩
  · exact ⟨FiniteK3Cases.C6N144.coeff,FiniteK3Cases.C6N144.valid⟩
  · exact ⟨FiniteK3Cases.C6N145.coeff,FiniteK3Cases.C6N145.valid⟩
  · exact ⟨FiniteK3Cases.C6N146.coeff,FiniteK3Cases.C6N146.valid⟩
  · exact ⟨FiniteK3Cases.C6N147.coeff,FiniteK3Cases.C6N147.valid⟩
  · exact ⟨FiniteK3Cases.C6N148.coeff,FiniteK3Cases.C6N148.valid⟩
  · exact ⟨FiniteK3Cases.C6N149.coeff,FiniteK3Cases.C6N149.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N134To149
