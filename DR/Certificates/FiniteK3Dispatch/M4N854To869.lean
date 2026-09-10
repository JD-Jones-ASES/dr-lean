import DR.Certificates.FiniteK3Cases.M4N854
import DR.Certificates.FiniteK3Cases.M4N855
import DR.Certificates.FiniteK3Cases.M4N856
import DR.Certificates.FiniteK3Cases.M4N857
import DR.Certificates.FiniteK3Cases.M4N858
import DR.Certificates.FiniteK3Cases.M4N859
import DR.Certificates.FiniteK3Cases.M4N860
import DR.Certificates.FiniteK3Cases.M4N861
import DR.Certificates.FiniteK3Cases.M4N862
import DR.Certificates.FiniteK3Cases.M4N863
import DR.Certificates.FiniteK3Cases.M4N864
import DR.Certificates.FiniteK3Cases.M4N865
import DR.Certificates.FiniteK3Cases.M4N866
import DR.Certificates.FiniteK3Cases.M4N867
import DR.Certificates.FiniteK3Cases.M4N868
import DR.Certificates.FiniteK3Cases.M4N869
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N854To869

theorem exists_valid (n : Nat) (hlo : 854≤n) (hhi : n≤869) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N854.coeff,FiniteK3Cases.C4N854.valid⟩
  · exact ⟨FiniteK3Cases.C4N855.coeff,FiniteK3Cases.C4N855.valid⟩
  · exact ⟨FiniteK3Cases.C4N856.coeff,FiniteK3Cases.C4N856.valid⟩
  · exact ⟨FiniteK3Cases.C4N857.coeff,FiniteK3Cases.C4N857.valid⟩
  · exact ⟨FiniteK3Cases.C4N858.coeff,FiniteK3Cases.C4N858.valid⟩
  · exact ⟨FiniteK3Cases.C4N859.coeff,FiniteK3Cases.C4N859.valid⟩
  · exact ⟨FiniteK3Cases.C4N860.coeff,FiniteK3Cases.C4N860.valid⟩
  · exact ⟨FiniteK3Cases.C4N861.coeff,FiniteK3Cases.C4N861.valid⟩
  · exact ⟨FiniteK3Cases.C4N862.coeff,FiniteK3Cases.C4N862.valid⟩
  · exact ⟨FiniteK3Cases.C4N863.coeff,FiniteK3Cases.C4N863.valid⟩
  · exact ⟨FiniteK3Cases.C4N864.coeff,FiniteK3Cases.C4N864.valid⟩
  · exact ⟨FiniteK3Cases.C4N865.coeff,FiniteK3Cases.C4N865.valid⟩
  · exact ⟨FiniteK3Cases.C4N866.coeff,FiniteK3Cases.C4N866.valid⟩
  · exact ⟨FiniteK3Cases.C4N867.coeff,FiniteK3Cases.C4N867.valid⟩
  · exact ⟨FiniteK3Cases.C4N868.coeff,FiniteK3Cases.C4N868.valid⟩
  · exact ⟨FiniteK3Cases.C4N869.coeff,FiniteK3Cases.C4N869.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N854To869
