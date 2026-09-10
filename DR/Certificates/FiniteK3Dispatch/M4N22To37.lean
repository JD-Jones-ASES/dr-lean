import DR.Certificates.FiniteK3Cases.M4N22
import DR.Certificates.FiniteK3Cases.M4N23
import DR.Certificates.FiniteK3Cases.M4N24
import DR.Certificates.FiniteK3Cases.M4N25
import DR.Certificates.FiniteK3Cases.M4N26
import DR.Certificates.FiniteK3Cases.M4N27
import DR.Certificates.FiniteK3Cases.M4N28
import DR.Certificates.FiniteK3Cases.M4N29
import DR.Certificates.FiniteK3Cases.M4N30
import DR.Certificates.FiniteK3Cases.M4N31
import DR.Certificates.FiniteK3Cases.M4N32
import DR.Certificates.FiniteK3Cases.M4N33
import DR.Certificates.FiniteK3Cases.M4N34
import DR.Certificates.FiniteK3Cases.M4N35
import DR.Certificates.FiniteK3Cases.M4N36
import DR.Certificates.FiniteK3Cases.M4N37
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N22To37

theorem exists_valid (n : Nat) (hlo : 22≤n) (hhi : n≤37) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N22.coeff,FiniteK3Cases.C4N22.valid⟩
  · exact ⟨FiniteK3Cases.C4N23.coeff,FiniteK3Cases.C4N23.valid⟩
  · exact ⟨FiniteK3Cases.C4N24.coeff,FiniteK3Cases.C4N24.valid⟩
  · exact ⟨FiniteK3Cases.C4N25.coeff,FiniteK3Cases.C4N25.valid⟩
  · exact ⟨FiniteK3Cases.C4N26.coeff,FiniteK3Cases.C4N26.valid⟩
  · exact ⟨FiniteK3Cases.C4N27.coeff,FiniteK3Cases.C4N27.valid⟩
  · exact ⟨FiniteK3Cases.C4N28.coeff,FiniteK3Cases.C4N28.valid⟩
  · exact ⟨FiniteK3Cases.C4N29.coeff,FiniteK3Cases.C4N29.valid⟩
  · exact ⟨FiniteK3Cases.C4N30.coeff,FiniteK3Cases.C4N30.valid⟩
  · exact ⟨FiniteK3Cases.C4N31.coeff,FiniteK3Cases.C4N31.valid⟩
  · exact ⟨FiniteK3Cases.C4N32.coeff,FiniteK3Cases.C4N32.valid⟩
  · exact ⟨FiniteK3Cases.C4N33.coeff,FiniteK3Cases.C4N33.valid⟩
  · exact ⟨FiniteK3Cases.C4N34.coeff,FiniteK3Cases.C4N34.valid⟩
  · exact ⟨FiniteK3Cases.C4N35.coeff,FiniteK3Cases.C4N35.valid⟩
  · exact ⟨FiniteK3Cases.C4N36.coeff,FiniteK3Cases.C4N36.valid⟩
  · exact ⟨FiniteK3Cases.C4N37.coeff,FiniteK3Cases.C4N37.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N22To37
