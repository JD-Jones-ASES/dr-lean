import DR.Certificates.FiniteK3Cases.M5N53
import DR.Certificates.FiniteK3Cases.M5N54
import DR.Certificates.FiniteK3Cases.M5N55
import DR.Certificates.FiniteK3Cases.M5N56
import DR.Certificates.FiniteK3Cases.M5N57
import DR.Certificates.FiniteK3Cases.M5N58
import DR.Certificates.FiniteK3Cases.M5N59
import DR.Certificates.FiniteK3Cases.M5N60
import DR.Certificates.FiniteK3Cases.M5N61
import DR.Certificates.FiniteK3Cases.M5N62
import DR.Certificates.FiniteK3Cases.M5N63
import DR.Certificates.FiniteK3Cases.M5N64
import DR.Certificates.FiniteK3Cases.M5N65
import DR.Certificates.FiniteK3Cases.M5N66
import DR.Certificates.FiniteK3Cases.M5N67
import DR.Certificates.FiniteK3Cases.M5N68
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N53To68

theorem exists_valid (n : Nat) (hlo : 53≤n) (hhi : n≤68) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N53.coeff,FiniteK3Cases.C5N53.valid⟩
  · exact ⟨FiniteK3Cases.C5N54.coeff,FiniteK3Cases.C5N54.valid⟩
  · exact ⟨FiniteK3Cases.C5N55.coeff,FiniteK3Cases.C5N55.valid⟩
  · exact ⟨FiniteK3Cases.C5N56.coeff,FiniteK3Cases.C5N56.valid⟩
  · exact ⟨FiniteK3Cases.C5N57.coeff,FiniteK3Cases.C5N57.valid⟩
  · exact ⟨FiniteK3Cases.C5N58.coeff,FiniteK3Cases.C5N58.valid⟩
  · exact ⟨FiniteK3Cases.C5N59.coeff,FiniteK3Cases.C5N59.valid⟩
  · exact ⟨FiniteK3Cases.C5N60.coeff,FiniteK3Cases.C5N60.valid⟩
  · exact ⟨FiniteK3Cases.C5N61.coeff,FiniteK3Cases.C5N61.valid⟩
  · exact ⟨FiniteK3Cases.C5N62.coeff,FiniteK3Cases.C5N62.valid⟩
  · exact ⟨FiniteK3Cases.C5N63.coeff,FiniteK3Cases.C5N63.valid⟩
  · exact ⟨FiniteK3Cases.C5N64.coeff,FiniteK3Cases.C5N64.valid⟩
  · exact ⟨FiniteK3Cases.C5N65.coeff,FiniteK3Cases.C5N65.valid⟩
  · exact ⟨FiniteK3Cases.C5N66.coeff,FiniteK3Cases.C5N66.valid⟩
  · exact ⟨FiniteK3Cases.C5N67.coeff,FiniteK3Cases.C5N67.valid⟩
  · exact ⟨FiniteK3Cases.C5N68.coeff,FiniteK3Cases.C5N68.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N53To68
