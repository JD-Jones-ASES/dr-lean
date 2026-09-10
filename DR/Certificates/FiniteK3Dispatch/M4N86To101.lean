import DR.Certificates.FiniteK3Cases.M4N86
import DR.Certificates.FiniteK3Cases.M4N87
import DR.Certificates.FiniteK3Cases.M4N88
import DR.Certificates.FiniteK3Cases.M4N89
import DR.Certificates.FiniteK3Cases.M4N90
import DR.Certificates.FiniteK3Cases.M4N91
import DR.Certificates.FiniteK3Cases.M4N92
import DR.Certificates.FiniteK3Cases.M4N93
import DR.Certificates.FiniteK3Cases.M4N94
import DR.Certificates.FiniteK3Cases.M4N95
import DR.Certificates.FiniteK3Cases.M4N96
import DR.Certificates.FiniteK3Cases.M4N97
import DR.Certificates.FiniteK3Cases.M4N98
import DR.Certificates.FiniteK3Cases.M4N99
import DR.Certificates.FiniteK3Cases.M4N100
import DR.Certificates.FiniteK3Cases.M4N101
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N86To101

theorem exists_valid (n : Nat) (hlo : 86≤n) (hhi : n≤101) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N86.coeff,FiniteK3Cases.C4N86.valid⟩
  · exact ⟨FiniteK3Cases.C4N87.coeff,FiniteK3Cases.C4N87.valid⟩
  · exact ⟨FiniteK3Cases.C4N88.coeff,FiniteK3Cases.C4N88.valid⟩
  · exact ⟨FiniteK3Cases.C4N89.coeff,FiniteK3Cases.C4N89.valid⟩
  · exact ⟨FiniteK3Cases.C4N90.coeff,FiniteK3Cases.C4N90.valid⟩
  · exact ⟨FiniteK3Cases.C4N91.coeff,FiniteK3Cases.C4N91.valid⟩
  · exact ⟨FiniteK3Cases.C4N92.coeff,FiniteK3Cases.C4N92.valid⟩
  · exact ⟨FiniteK3Cases.C4N93.coeff,FiniteK3Cases.C4N93.valid⟩
  · exact ⟨FiniteK3Cases.C4N94.coeff,FiniteK3Cases.C4N94.valid⟩
  · exact ⟨FiniteK3Cases.C4N95.coeff,FiniteK3Cases.C4N95.valid⟩
  · exact ⟨FiniteK3Cases.C4N96.coeff,FiniteK3Cases.C4N96.valid⟩
  · exact ⟨FiniteK3Cases.C4N97.coeff,FiniteK3Cases.C4N97.valid⟩
  · exact ⟨FiniteK3Cases.C4N98.coeff,FiniteK3Cases.C4N98.valid⟩
  · exact ⟨FiniteK3Cases.C4N99.coeff,FiniteK3Cases.C4N99.valid⟩
  · exact ⟨FiniteK3Cases.C4N100.coeff,FiniteK3Cases.C4N100.valid⟩
  · exact ⟨FiniteK3Cases.C4N101.coeff,FiniteK3Cases.C4N101.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N86To101
