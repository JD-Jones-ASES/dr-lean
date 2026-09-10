import DR.Certificates.FiniteK3Cases.M5N21
import DR.Certificates.FiniteK3Cases.M5N22
import DR.Certificates.FiniteK3Cases.M5N23
import DR.Certificates.FiniteK3Cases.M5N24
import DR.Certificates.FiniteK3Cases.M5N25
import DR.Certificates.FiniteK3Cases.M5N26
import DR.Certificates.FiniteK3Cases.M5N27
import DR.Certificates.FiniteK3Cases.M5N28
import DR.Certificates.FiniteK3Cases.M5N29
import DR.Certificates.FiniteK3Cases.M5N30
import DR.Certificates.FiniteK3Cases.M5N31
import DR.Certificates.FiniteK3Cases.M5N32
import DR.Certificates.FiniteK3Cases.M5N33
import DR.Certificates.FiniteK3Cases.M5N34
import DR.Certificates.FiniteK3Cases.M5N35
import DR.Certificates.FiniteK3Cases.M5N36
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N21To36

theorem exists_valid (n : Nat) (hlo : 21≤n) (hhi : n≤36) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N21.coeff,FiniteK3Cases.C5N21.valid⟩
  · exact ⟨FiniteK3Cases.C5N22.coeff,FiniteK3Cases.C5N22.valid⟩
  · exact ⟨FiniteK3Cases.C5N23.coeff,FiniteK3Cases.C5N23.valid⟩
  · exact ⟨FiniteK3Cases.C5N24.coeff,FiniteK3Cases.C5N24.valid⟩
  · exact ⟨FiniteK3Cases.C5N25.coeff,FiniteK3Cases.C5N25.valid⟩
  · exact ⟨FiniteK3Cases.C5N26.coeff,FiniteK3Cases.C5N26.valid⟩
  · exact ⟨FiniteK3Cases.C5N27.coeff,FiniteK3Cases.C5N27.valid⟩
  · exact ⟨FiniteK3Cases.C5N28.coeff,FiniteK3Cases.C5N28.valid⟩
  · exact ⟨FiniteK3Cases.C5N29.coeff,FiniteK3Cases.C5N29.valid⟩
  · exact ⟨FiniteK3Cases.C5N30.coeff,FiniteK3Cases.C5N30.valid⟩
  · exact ⟨FiniteK3Cases.C5N31.coeff,FiniteK3Cases.C5N31.valid⟩
  · exact ⟨FiniteK3Cases.C5N32.coeff,FiniteK3Cases.C5N32.valid⟩
  · exact ⟨FiniteK3Cases.C5N33.coeff,FiniteK3Cases.C5N33.valid⟩
  · exact ⟨FiniteK3Cases.C5N34.coeff,FiniteK3Cases.C5N34.valid⟩
  · exact ⟨FiniteK3Cases.C5N35.coeff,FiniteK3Cases.C5N35.valid⟩
  · exact ⟨FiniteK3Cases.C5N36.coeff,FiniteK3Cases.C5N36.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N21To36
