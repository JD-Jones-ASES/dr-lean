import DR.Certificates.FiniteK3Cases.M4N246
import DR.Certificates.FiniteK3Cases.M4N247
import DR.Certificates.FiniteK3Cases.M4N248
import DR.Certificates.FiniteK3Cases.M4N249
import DR.Certificates.FiniteK3Cases.M4N250
import DR.Certificates.FiniteK3Cases.M4N251
import DR.Certificates.FiniteK3Cases.M4N252
import DR.Certificates.FiniteK3Cases.M4N253
import DR.Certificates.FiniteK3Cases.M4N254
import DR.Certificates.FiniteK3Cases.M4N255
import DR.Certificates.FiniteK3Cases.M4N256
import DR.Certificates.FiniteK3Cases.M4N257
import DR.Certificates.FiniteK3Cases.M4N258
import DR.Certificates.FiniteK3Cases.M4N259
import DR.Certificates.FiniteK3Cases.M4N260
import DR.Certificates.FiniteK3Cases.M4N261
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N246To261

theorem exists_valid (n : Nat) (hlo : 246≤n) (hhi : n≤261) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N246.coeff,FiniteK3Cases.C4N246.valid⟩
  · exact ⟨FiniteK3Cases.C4N247.coeff,FiniteK3Cases.C4N247.valid⟩
  · exact ⟨FiniteK3Cases.C4N248.coeff,FiniteK3Cases.C4N248.valid⟩
  · exact ⟨FiniteK3Cases.C4N249.coeff,FiniteK3Cases.C4N249.valid⟩
  · exact ⟨FiniteK3Cases.C4N250.coeff,FiniteK3Cases.C4N250.valid⟩
  · exact ⟨FiniteK3Cases.C4N251.coeff,FiniteK3Cases.C4N251.valid⟩
  · exact ⟨FiniteK3Cases.C4N252.coeff,FiniteK3Cases.C4N252.valid⟩
  · exact ⟨FiniteK3Cases.C4N253.coeff,FiniteK3Cases.C4N253.valid⟩
  · exact ⟨FiniteK3Cases.C4N254.coeff,FiniteK3Cases.C4N254.valid⟩
  · exact ⟨FiniteK3Cases.C4N255.coeff,FiniteK3Cases.C4N255.valid⟩
  · exact ⟨FiniteK3Cases.C4N256.coeff,FiniteK3Cases.C4N256.valid⟩
  · exact ⟨FiniteK3Cases.C4N257.coeff,FiniteK3Cases.C4N257.valid⟩
  · exact ⟨FiniteK3Cases.C4N258.coeff,FiniteK3Cases.C4N258.valid⟩
  · exact ⟨FiniteK3Cases.C4N259.coeff,FiniteK3Cases.C4N259.valid⟩
  · exact ⟨FiniteK3Cases.C4N260.coeff,FiniteK3Cases.C4N260.valid⟩
  · exact ⟨FiniteK3Cases.C4N261.coeff,FiniteK3Cases.C4N261.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N246To261
