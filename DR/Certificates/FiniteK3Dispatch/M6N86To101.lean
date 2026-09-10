import DR.Certificates.FiniteK3Cases.M6N86
import DR.Certificates.FiniteK3Cases.M6N87
import DR.Certificates.FiniteK3Cases.M6N88
import DR.Certificates.FiniteK3Cases.M6N89
import DR.Certificates.FiniteK3Cases.M6N90
import DR.Certificates.FiniteK3Cases.M6N91
import DR.Certificates.FiniteK3Cases.M6N92
import DR.Certificates.FiniteK3Cases.M6N93
import DR.Certificates.FiniteK3Cases.M6N94
import DR.Certificates.FiniteK3Cases.M6N95
import DR.Certificates.FiniteK3Cases.M6N96
import DR.Certificates.FiniteK3Cases.M6N97
import DR.Certificates.FiniteK3Cases.M6N98
import DR.Certificates.FiniteK3Cases.M6N99
import DR.Certificates.FiniteK3Cases.M6N100
import DR.Certificates.FiniteK3Cases.M6N101
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N86To101

theorem exists_valid (n : Nat) (hlo : 86≤n) (hhi : n≤101) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N86.coeff,FiniteK3Cases.C6N86.valid⟩
  · exact ⟨FiniteK3Cases.C6N87.coeff,FiniteK3Cases.C6N87.valid⟩
  · exact ⟨FiniteK3Cases.C6N88.coeff,FiniteK3Cases.C6N88.valid⟩
  · exact ⟨FiniteK3Cases.C6N89.coeff,FiniteK3Cases.C6N89.valid⟩
  · exact ⟨FiniteK3Cases.C6N90.coeff,FiniteK3Cases.C6N90.valid⟩
  · exact ⟨FiniteK3Cases.C6N91.coeff,FiniteK3Cases.C6N91.valid⟩
  · exact ⟨FiniteK3Cases.C6N92.coeff,FiniteK3Cases.C6N92.valid⟩
  · exact ⟨FiniteK3Cases.C6N93.coeff,FiniteK3Cases.C6N93.valid⟩
  · exact ⟨FiniteK3Cases.C6N94.coeff,FiniteK3Cases.C6N94.valid⟩
  · exact ⟨FiniteK3Cases.C6N95.coeff,FiniteK3Cases.C6N95.valid⟩
  · exact ⟨FiniteK3Cases.C6N96.coeff,FiniteK3Cases.C6N96.valid⟩
  · exact ⟨FiniteK3Cases.C6N97.coeff,FiniteK3Cases.C6N97.valid⟩
  · exact ⟨FiniteK3Cases.C6N98.coeff,FiniteK3Cases.C6N98.valid⟩
  · exact ⟨FiniteK3Cases.C6N99.coeff,FiniteK3Cases.C6N99.valid⟩
  · exact ⟨FiniteK3Cases.C6N100.coeff,FiniteK3Cases.C6N100.valid⟩
  · exact ⟨FiniteK3Cases.C6N101.coeff,FiniteK3Cases.C6N101.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N86To101
