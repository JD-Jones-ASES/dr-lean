import DR.Certificates.FiniteK3Cases.M4N38
import DR.Certificates.FiniteK3Cases.M4N39
import DR.Certificates.FiniteK3Cases.M4N40
import DR.Certificates.FiniteK3Cases.M4N41
import DR.Certificates.FiniteK3Cases.M4N42
import DR.Certificates.FiniteK3Cases.M4N43
import DR.Certificates.FiniteK3Cases.M4N44
import DR.Certificates.FiniteK3Cases.M4N45
import DR.Certificates.FiniteK3Cases.M4N46
import DR.Certificates.FiniteK3Cases.M4N47
import DR.Certificates.FiniteK3Cases.M4N48
import DR.Certificates.FiniteK3Cases.M4N49
import DR.Certificates.FiniteK3Cases.M4N50
import DR.Certificates.FiniteK3Cases.M4N51
import DR.Certificates.FiniteK3Cases.M4N52
import DR.Certificates.FiniteK3Cases.M4N53
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N38To53

theorem exists_valid (n : Nat) (hlo : 38≤n) (hhi : n≤53) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N38.coeff,FiniteK3Cases.C4N38.valid⟩
  · exact ⟨FiniteK3Cases.C4N39.coeff,FiniteK3Cases.C4N39.valid⟩
  · exact ⟨FiniteK3Cases.C4N40.coeff,FiniteK3Cases.C4N40.valid⟩
  · exact ⟨FiniteK3Cases.C4N41.coeff,FiniteK3Cases.C4N41.valid⟩
  · exact ⟨FiniteK3Cases.C4N42.coeff,FiniteK3Cases.C4N42.valid⟩
  · exact ⟨FiniteK3Cases.C4N43.coeff,FiniteK3Cases.C4N43.valid⟩
  · exact ⟨FiniteK3Cases.C4N44.coeff,FiniteK3Cases.C4N44.valid⟩
  · exact ⟨FiniteK3Cases.C4N45.coeff,FiniteK3Cases.C4N45.valid⟩
  · exact ⟨FiniteK3Cases.C4N46.coeff,FiniteK3Cases.C4N46.valid⟩
  · exact ⟨FiniteK3Cases.C4N47.coeff,FiniteK3Cases.C4N47.valid⟩
  · exact ⟨FiniteK3Cases.C4N48.coeff,FiniteK3Cases.C4N48.valid⟩
  · exact ⟨FiniteK3Cases.C4N49.coeff,FiniteK3Cases.C4N49.valid⟩
  · exact ⟨FiniteK3Cases.C4N50.coeff,FiniteK3Cases.C4N50.valid⟩
  · exact ⟨FiniteK3Cases.C4N51.coeff,FiniteK3Cases.C4N51.valid⟩
  · exact ⟨FiniteK3Cases.C4N52.coeff,FiniteK3Cases.C4N52.valid⟩
  · exact ⟨FiniteK3Cases.C4N53.coeff,FiniteK3Cases.C4N53.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N38To53
