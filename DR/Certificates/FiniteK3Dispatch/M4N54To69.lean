import DR.Certificates.FiniteK3Cases.M4N54
import DR.Certificates.FiniteK3Cases.M4N55
import DR.Certificates.FiniteK3Cases.M4N56
import DR.Certificates.FiniteK3Cases.M4N57
import DR.Certificates.FiniteK3Cases.M4N58
import DR.Certificates.FiniteK3Cases.M4N59
import DR.Certificates.FiniteK3Cases.M4N60
import DR.Certificates.FiniteK3Cases.M4N61
import DR.Certificates.FiniteK3Cases.M4N62
import DR.Certificates.FiniteK3Cases.M4N63
import DR.Certificates.FiniteK3Cases.M4N64
import DR.Certificates.FiniteK3Cases.M4N65
import DR.Certificates.FiniteK3Cases.M4N66
import DR.Certificates.FiniteK3Cases.M4N67
import DR.Certificates.FiniteK3Cases.M4N68
import DR.Certificates.FiniteK3Cases.M4N69
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N54To69

theorem exists_valid (n : Nat) (hlo : 54≤n) (hhi : n≤69) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N54.coeff,FiniteK3Cases.C4N54.valid⟩
  · exact ⟨FiniteK3Cases.C4N55.coeff,FiniteK3Cases.C4N55.valid⟩
  · exact ⟨FiniteK3Cases.C4N56.coeff,FiniteK3Cases.C4N56.valid⟩
  · exact ⟨FiniteK3Cases.C4N57.coeff,FiniteK3Cases.C4N57.valid⟩
  · exact ⟨FiniteK3Cases.C4N58.coeff,FiniteK3Cases.C4N58.valid⟩
  · exact ⟨FiniteK3Cases.C4N59.coeff,FiniteK3Cases.C4N59.valid⟩
  · exact ⟨FiniteK3Cases.C4N60.coeff,FiniteK3Cases.C4N60.valid⟩
  · exact ⟨FiniteK3Cases.C4N61.coeff,FiniteK3Cases.C4N61.valid⟩
  · exact ⟨FiniteK3Cases.C4N62.coeff,FiniteK3Cases.C4N62.valid⟩
  · exact ⟨FiniteK3Cases.C4N63.coeff,FiniteK3Cases.C4N63.valid⟩
  · exact ⟨FiniteK3Cases.C4N64.coeff,FiniteK3Cases.C4N64.valid⟩
  · exact ⟨FiniteK3Cases.C4N65.coeff,FiniteK3Cases.C4N65.valid⟩
  · exact ⟨FiniteK3Cases.C4N66.coeff,FiniteK3Cases.C4N66.valid⟩
  · exact ⟨FiniteK3Cases.C4N67.coeff,FiniteK3Cases.C4N67.valid⟩
  · exact ⟨FiniteK3Cases.C4N68.coeff,FiniteK3Cases.C4N68.valid⟩
  · exact ⟨FiniteK3Cases.C4N69.coeff,FiniteK3Cases.C4N69.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N54To69
