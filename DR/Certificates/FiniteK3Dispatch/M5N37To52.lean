import DR.Certificates.FiniteK3Cases.M5N37
import DR.Certificates.FiniteK3Cases.M5N38
import DR.Certificates.FiniteK3Cases.M5N39
import DR.Certificates.FiniteK3Cases.M5N40
import DR.Certificates.FiniteK3Cases.M5N41
import DR.Certificates.FiniteK3Cases.M5N42
import DR.Certificates.FiniteK3Cases.M5N43
import DR.Certificates.FiniteK3Cases.M5N44
import DR.Certificates.FiniteK3Cases.M5N45
import DR.Certificates.FiniteK3Cases.M5N46
import DR.Certificates.FiniteK3Cases.M5N47
import DR.Certificates.FiniteK3Cases.M5N48
import DR.Certificates.FiniteK3Cases.M5N49
import DR.Certificates.FiniteK3Cases.M5N50
import DR.Certificates.FiniteK3Cases.M5N51
import DR.Certificates.FiniteK3Cases.M5N52
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C5N37To52

theorem exists_valid (n : Nat) (hlo : 37≤n) (hhi : n≤52) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 5 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C5N37.coeff,FiniteK3Cases.C5N37.valid⟩
  · exact ⟨FiniteK3Cases.C5N38.coeff,FiniteK3Cases.C5N38.valid⟩
  · exact ⟨FiniteK3Cases.C5N39.coeff,FiniteK3Cases.C5N39.valid⟩
  · exact ⟨FiniteK3Cases.C5N40.coeff,FiniteK3Cases.C5N40.valid⟩
  · exact ⟨FiniteK3Cases.C5N41.coeff,FiniteK3Cases.C5N41.valid⟩
  · exact ⟨FiniteK3Cases.C5N42.coeff,FiniteK3Cases.C5N42.valid⟩
  · exact ⟨FiniteK3Cases.C5N43.coeff,FiniteK3Cases.C5N43.valid⟩
  · exact ⟨FiniteK3Cases.C5N44.coeff,FiniteK3Cases.C5N44.valid⟩
  · exact ⟨FiniteK3Cases.C5N45.coeff,FiniteK3Cases.C5N45.valid⟩
  · exact ⟨FiniteK3Cases.C5N46.coeff,FiniteK3Cases.C5N46.valid⟩
  · exact ⟨FiniteK3Cases.C5N47.coeff,FiniteK3Cases.C5N47.valid⟩
  · exact ⟨FiniteK3Cases.C5N48.coeff,FiniteK3Cases.C5N48.valid⟩
  · exact ⟨FiniteK3Cases.C5N49.coeff,FiniteK3Cases.C5N49.valid⟩
  · exact ⟨FiniteK3Cases.C5N50.coeff,FiniteK3Cases.C5N50.valid⟩
  · exact ⟨FiniteK3Cases.C5N51.coeff,FiniteK3Cases.C5N51.valid⟩
  · exact ⟨FiniteK3Cases.C5N52.coeff,FiniteK3Cases.C5N52.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C5N37To52
