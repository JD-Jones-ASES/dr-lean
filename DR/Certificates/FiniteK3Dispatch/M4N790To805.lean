import DR.Certificates.FiniteK3Cases.M4N790
import DR.Certificates.FiniteK3Cases.M4N791
import DR.Certificates.FiniteK3Cases.M4N792
import DR.Certificates.FiniteK3Cases.M4N793
import DR.Certificates.FiniteK3Cases.M4N794
import DR.Certificates.FiniteK3Cases.M4N795
import DR.Certificates.FiniteK3Cases.M4N796
import DR.Certificates.FiniteK3Cases.M4N797
import DR.Certificates.FiniteK3Cases.M4N798
import DR.Certificates.FiniteK3Cases.M4N799
import DR.Certificates.FiniteK3Cases.M4N800
import DR.Certificates.FiniteK3Cases.M4N801
import DR.Certificates.FiniteK3Cases.M4N802
import DR.Certificates.FiniteK3Cases.M4N803
import DR.Certificates.FiniteK3Cases.M4N804
import DR.Certificates.FiniteK3Cases.M4N805
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N790To805

theorem exists_valid (n : Nat) (hlo : 790≤n) (hhi : n≤805) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N790.coeff,FiniteK3Cases.C4N790.valid⟩
  · exact ⟨FiniteK3Cases.C4N791.coeff,FiniteK3Cases.C4N791.valid⟩
  · exact ⟨FiniteK3Cases.C4N792.coeff,FiniteK3Cases.C4N792.valid⟩
  · exact ⟨FiniteK3Cases.C4N793.coeff,FiniteK3Cases.C4N793.valid⟩
  · exact ⟨FiniteK3Cases.C4N794.coeff,FiniteK3Cases.C4N794.valid⟩
  · exact ⟨FiniteK3Cases.C4N795.coeff,FiniteK3Cases.C4N795.valid⟩
  · exact ⟨FiniteK3Cases.C4N796.coeff,FiniteK3Cases.C4N796.valid⟩
  · exact ⟨FiniteK3Cases.C4N797.coeff,FiniteK3Cases.C4N797.valid⟩
  · exact ⟨FiniteK3Cases.C4N798.coeff,FiniteK3Cases.C4N798.valid⟩
  · exact ⟨FiniteK3Cases.C4N799.coeff,FiniteK3Cases.C4N799.valid⟩
  · exact ⟨FiniteK3Cases.C4N800.coeff,FiniteK3Cases.C4N800.valid⟩
  · exact ⟨FiniteK3Cases.C4N801.coeff,FiniteK3Cases.C4N801.valid⟩
  · exact ⟨FiniteK3Cases.C4N802.coeff,FiniteK3Cases.C4N802.valid⟩
  · exact ⟨FiniteK3Cases.C4N803.coeff,FiniteK3Cases.C4N803.valid⟩
  · exact ⟨FiniteK3Cases.C4N804.coeff,FiniteK3Cases.C4N804.valid⟩
  · exact ⟨FiniteK3Cases.C4N805.coeff,FiniteK3Cases.C4N805.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N790To805
