import DR.Certificates.FiniteK3Cases.M6N38
import DR.Certificates.FiniteK3Cases.M6N39
import DR.Certificates.FiniteK3Cases.M6N40
import DR.Certificates.FiniteK3Cases.M6N41
import DR.Certificates.FiniteK3Cases.M6N42
import DR.Certificates.FiniteK3Cases.M6N43
import DR.Certificates.FiniteK3Cases.M6N44
import DR.Certificates.FiniteK3Cases.M6N45
import DR.Certificates.FiniteK3Cases.M6N46
import DR.Certificates.FiniteK3Cases.M6N47
import DR.Certificates.FiniteK3Cases.M6N48
import DR.Certificates.FiniteK3Cases.M6N49
import DR.Certificates.FiniteK3Cases.M6N50
import DR.Certificates.FiniteK3Cases.M6N51
import DR.Certificates.FiniteK3Cases.M6N52
import DR.Certificates.FiniteK3Cases.M6N53
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C6N38To53

theorem exists_valid (n : Nat) (hlo : 38≤n) (hhi : n≤53) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 6 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C6N38.coeff,FiniteK3Cases.C6N38.valid⟩
  · exact ⟨FiniteK3Cases.C6N39.coeff,FiniteK3Cases.C6N39.valid⟩
  · exact ⟨FiniteK3Cases.C6N40.coeff,FiniteK3Cases.C6N40.valid⟩
  · exact ⟨FiniteK3Cases.C6N41.coeff,FiniteK3Cases.C6N41.valid⟩
  · exact ⟨FiniteK3Cases.C6N42.coeff,FiniteK3Cases.C6N42.valid⟩
  · exact ⟨FiniteK3Cases.C6N43.coeff,FiniteK3Cases.C6N43.valid⟩
  · exact ⟨FiniteK3Cases.C6N44.coeff,FiniteK3Cases.C6N44.valid⟩
  · exact ⟨FiniteK3Cases.C6N45.coeff,FiniteK3Cases.C6N45.valid⟩
  · exact ⟨FiniteK3Cases.C6N46.coeff,FiniteK3Cases.C6N46.valid⟩
  · exact ⟨FiniteK3Cases.C6N47.coeff,FiniteK3Cases.C6N47.valid⟩
  · exact ⟨FiniteK3Cases.C6N48.coeff,FiniteK3Cases.C6N48.valid⟩
  · exact ⟨FiniteK3Cases.C6N49.coeff,FiniteK3Cases.C6N49.valid⟩
  · exact ⟨FiniteK3Cases.C6N50.coeff,FiniteK3Cases.C6N50.valid⟩
  · exact ⟨FiniteK3Cases.C6N51.coeff,FiniteK3Cases.C6N51.valid⟩
  · exact ⟨FiniteK3Cases.C6N52.coeff,FiniteK3Cases.C6N52.valid⟩
  · exact ⟨FiniteK3Cases.C6N53.coeff,FiniteK3Cases.C6N53.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C6N38To53
