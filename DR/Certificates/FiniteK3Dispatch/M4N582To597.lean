import DR.Certificates.FiniteK3Cases.M4N582
import DR.Certificates.FiniteK3Cases.M4N583
import DR.Certificates.FiniteK3Cases.M4N584
import DR.Certificates.FiniteK3Cases.M4N585
import DR.Certificates.FiniteK3Cases.M4N586
import DR.Certificates.FiniteK3Cases.M4N587
import DR.Certificates.FiniteK3Cases.M4N588
import DR.Certificates.FiniteK3Cases.M4N589
import DR.Certificates.FiniteK3Cases.M4N590
import DR.Certificates.FiniteK3Cases.M4N591
import DR.Certificates.FiniteK3Cases.M4N592
import DR.Certificates.FiniteK3Cases.M4N593
import DR.Certificates.FiniteK3Cases.M4N594
import DR.Certificates.FiniteK3Cases.M4N595
import DR.Certificates.FiniteK3Cases.M4N596
import DR.Certificates.FiniteK3Cases.M4N597
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N582To597

theorem exists_valid (n : Nat) (hlo : 582≤n) (hhi : n≤597) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N582.coeff,FiniteK3Cases.C4N582.valid⟩
  · exact ⟨FiniteK3Cases.C4N583.coeff,FiniteK3Cases.C4N583.valid⟩
  · exact ⟨FiniteK3Cases.C4N584.coeff,FiniteK3Cases.C4N584.valid⟩
  · exact ⟨FiniteK3Cases.C4N585.coeff,FiniteK3Cases.C4N585.valid⟩
  · exact ⟨FiniteK3Cases.C4N586.coeff,FiniteK3Cases.C4N586.valid⟩
  · exact ⟨FiniteK3Cases.C4N587.coeff,FiniteK3Cases.C4N587.valid⟩
  · exact ⟨FiniteK3Cases.C4N588.coeff,FiniteK3Cases.C4N588.valid⟩
  · exact ⟨FiniteK3Cases.C4N589.coeff,FiniteK3Cases.C4N589.valid⟩
  · exact ⟨FiniteK3Cases.C4N590.coeff,FiniteK3Cases.C4N590.valid⟩
  · exact ⟨FiniteK3Cases.C4N591.coeff,FiniteK3Cases.C4N591.valid⟩
  · exact ⟨FiniteK3Cases.C4N592.coeff,FiniteK3Cases.C4N592.valid⟩
  · exact ⟨FiniteK3Cases.C4N593.coeff,FiniteK3Cases.C4N593.valid⟩
  · exact ⟨FiniteK3Cases.C4N594.coeff,FiniteK3Cases.C4N594.valid⟩
  · exact ⟨FiniteK3Cases.C4N595.coeff,FiniteK3Cases.C4N595.valid⟩
  · exact ⟨FiniteK3Cases.C4N596.coeff,FiniteK3Cases.C4N596.valid⟩
  · exact ⟨FiniteK3Cases.C4N597.coeff,FiniteK3Cases.C4N597.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N582To597
