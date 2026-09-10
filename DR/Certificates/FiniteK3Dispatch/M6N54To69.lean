import DR.Certificates.FiniteK3Cases.M6N54
import DR.Certificates.FiniteK3Cases.M6N55
import DR.Certificates.FiniteK3Cases.M6N56
import DR.Certificates.FiniteK3Cases.M6N57
import DR.Certificates.FiniteK3Cases.M6N58
import DR.Certificates.FiniteK3Cases.M6N59
import DR.Certificates.FiniteK3Cases.M6N60
import DR.Certificates.FiniteK3Cases.M6N61
import DR.Certificates.FiniteK3Cases.M6N62
import DR.Certificates.FiniteK3Cases.M6N63
import DR.Certificates.FiniteK3Cases.M6N64
import DR.Certificates.FiniteK3Cases.M6N65
import DR.Certificates.FiniteK3Cases.M6N66
import DR.Certificates.FiniteK3Cases.M6N67
import DR.Certificates.FiniteK3Cases.M6N68
import DR.Certificates.FiniteK3Cases.M6N69
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N54To69

theorem exists_valid (n : Nat) (hlo : 54≤n) (hhi : n≤69) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N54.coeff,FiniteK3Cases.C6N54.valid⟩
  · exact ⟨FiniteK3Cases.C6N55.coeff,FiniteK3Cases.C6N55.valid⟩
  · exact ⟨FiniteK3Cases.C6N56.coeff,FiniteK3Cases.C6N56.valid⟩
  · exact ⟨FiniteK3Cases.C6N57.coeff,FiniteK3Cases.C6N57.valid⟩
  · exact ⟨FiniteK3Cases.C6N58.coeff,FiniteK3Cases.C6N58.valid⟩
  · exact ⟨FiniteK3Cases.C6N59.coeff,FiniteK3Cases.C6N59.valid⟩
  · exact ⟨FiniteK3Cases.C6N60.coeff,FiniteK3Cases.C6N60.valid⟩
  · exact ⟨FiniteK3Cases.C6N61.coeff,FiniteK3Cases.C6N61.valid⟩
  · exact ⟨FiniteK3Cases.C6N62.coeff,FiniteK3Cases.C6N62.valid⟩
  · exact ⟨FiniteK3Cases.C6N63.coeff,FiniteK3Cases.C6N63.valid⟩
  · exact ⟨FiniteK3Cases.C6N64.coeff,FiniteK3Cases.C6N64.valid⟩
  · exact ⟨FiniteK3Cases.C6N65.coeff,FiniteK3Cases.C6N65.valid⟩
  · exact ⟨FiniteK3Cases.C6N66.coeff,FiniteK3Cases.C6N66.valid⟩
  · exact ⟨FiniteK3Cases.C6N67.coeff,FiniteK3Cases.C6N67.valid⟩
  · exact ⟨FiniteK3Cases.C6N68.coeff,FiniteK3Cases.C6N68.valid⟩
  · exact ⟨FiniteK3Cases.C6N69.coeff,FiniteK3Cases.C6N69.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N54To69
