import DR.Certificates.FiniteK3Cases.M6N22
import DR.Certificates.FiniteK3Cases.M6N23
import DR.Certificates.FiniteK3Cases.M6N24
import DR.Certificates.FiniteK3Cases.M6N25
import DR.Certificates.FiniteK3Cases.M6N26
import DR.Certificates.FiniteK3Cases.M6N27
import DR.Certificates.FiniteK3Cases.M6N28
import DR.Certificates.FiniteK3Cases.M6N29
import DR.Certificates.FiniteK3Cases.M6N30
import DR.Certificates.FiniteK3Cases.M6N31
import DR.Certificates.FiniteK3Cases.M6N32
import DR.Certificates.FiniteK3Cases.M6N33
import DR.Certificates.FiniteK3Cases.M6N34
import DR.Certificates.FiniteK3Cases.M6N35
import DR.Certificates.FiniteK3Cases.M6N36
import DR.Certificates.FiniteK3Cases.M6N37
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N22To37

theorem exists_valid (n : Nat) (hlo : 22≤n) (hhi : n≤37) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N22.coeff,FiniteK3Cases.C6N22.valid⟩
  · exact ⟨FiniteK3Cases.C6N23.coeff,FiniteK3Cases.C6N23.valid⟩
  · exact ⟨FiniteK3Cases.C6N24.coeff,FiniteK3Cases.C6N24.valid⟩
  · exact ⟨FiniteK3Cases.C6N25.coeff,FiniteK3Cases.C6N25.valid⟩
  · exact ⟨FiniteK3Cases.C6N26.coeff,FiniteK3Cases.C6N26.valid⟩
  · exact ⟨FiniteK3Cases.C6N27.coeff,FiniteK3Cases.C6N27.valid⟩
  · exact ⟨FiniteK3Cases.C6N28.coeff,FiniteK3Cases.C6N28.valid⟩
  · exact ⟨FiniteK3Cases.C6N29.coeff,FiniteK3Cases.C6N29.valid⟩
  · exact ⟨FiniteK3Cases.C6N30.coeff,FiniteK3Cases.C6N30.valid⟩
  · exact ⟨FiniteK3Cases.C6N31.coeff,FiniteK3Cases.C6N31.valid⟩
  · exact ⟨FiniteK3Cases.C6N32.coeff,FiniteK3Cases.C6N32.valid⟩
  · exact ⟨FiniteK3Cases.C6N33.coeff,FiniteK3Cases.C6N33.valid⟩
  · exact ⟨FiniteK3Cases.C6N34.coeff,FiniteK3Cases.C6N34.valid⟩
  · exact ⟨FiniteK3Cases.C6N35.coeff,FiniteK3Cases.C6N35.valid⟩
  · exact ⟨FiniteK3Cases.C6N36.coeff,FiniteK3Cases.C6N36.valid⟩
  · exact ⟨FiniteK3Cases.C6N37.coeff,FiniteK3Cases.C6N37.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N22To37
