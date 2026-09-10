import DR.Certificates.FiniteK3Cases.M5N85
import DR.Certificates.FiniteK3Cases.M5N86
import DR.Certificates.FiniteK3Cases.M5N87
import DR.Certificates.FiniteK3Cases.M5N88
import DR.Certificates.FiniteK3Cases.M5N89
import DR.Certificates.FiniteK3Cases.M5N90
import DR.Certificates.FiniteK3Cases.M5N91
import DR.Certificates.FiniteK3Cases.M5N92
import DR.Certificates.FiniteK3Cases.M5N93
import DR.Certificates.FiniteK3Cases.M5N94
import DR.Certificates.FiniteK3Cases.M5N95
import DR.Certificates.FiniteK3Cases.M5N96
import DR.Certificates.FiniteK3Cases.M5N97
import DR.Certificates.FiniteK3Cases.M5N98
import DR.Certificates.FiniteK3Cases.M5N99
import DR.Certificates.FiniteK3Cases.M5N100
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N85To100

theorem exists_valid (n : Nat) (hlo : 85≤n) (hhi : n≤100) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N85.coeff,FiniteK3Cases.C5N85.valid⟩
  · exact ⟨FiniteK3Cases.C5N86.coeff,FiniteK3Cases.C5N86.valid⟩
  · exact ⟨FiniteK3Cases.C5N87.coeff,FiniteK3Cases.C5N87.valid⟩
  · exact ⟨FiniteK3Cases.C5N88.coeff,FiniteK3Cases.C5N88.valid⟩
  · exact ⟨FiniteK3Cases.C5N89.coeff,FiniteK3Cases.C5N89.valid⟩
  · exact ⟨FiniteK3Cases.C5N90.coeff,FiniteK3Cases.C5N90.valid⟩
  · exact ⟨FiniteK3Cases.C5N91.coeff,FiniteK3Cases.C5N91.valid⟩
  · exact ⟨FiniteK3Cases.C5N92.coeff,FiniteK3Cases.C5N92.valid⟩
  · exact ⟨FiniteK3Cases.C5N93.coeff,FiniteK3Cases.C5N93.valid⟩
  · exact ⟨FiniteK3Cases.C5N94.coeff,FiniteK3Cases.C5N94.valid⟩
  · exact ⟨FiniteK3Cases.C5N95.coeff,FiniteK3Cases.C5N95.valid⟩
  · exact ⟨FiniteK3Cases.C5N96.coeff,FiniteK3Cases.C5N96.valid⟩
  · exact ⟨FiniteK3Cases.C5N97.coeff,FiniteK3Cases.C5N97.valid⟩
  · exact ⟨FiniteK3Cases.C5N98.coeff,FiniteK3Cases.C5N98.valid⟩
  · exact ⟨FiniteK3Cases.C5N99.coeff,FiniteK3Cases.C5N99.valid⟩
  · exact ⟨FiniteK3Cases.C5N100.coeff,FiniteK3Cases.C5N100.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N85To100
