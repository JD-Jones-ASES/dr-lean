import DR.Certificates.FiniteK3Cases.M4N918
import DR.Certificates.FiniteK3Cases.M4N919
import DR.Certificates.FiniteK3Cases.M4N920
import DR.Certificates.FiniteK3Cases.M4N921
import DR.Certificates.FiniteK3Cases.M4N922
import DR.Certificates.FiniteK3Cases.M4N923
import DR.Certificates.FiniteK3Cases.M4N924
import DR.Certificates.FiniteK3Cases.M4N925
import DR.Certificates.FiniteK3Cases.M4N926
import DR.Certificates.FiniteK3Cases.M4N927
import DR.Certificates.FiniteK3Cases.M4N928
import DR.Certificates.FiniteK3Cases.M4N929
import DR.Certificates.FiniteK3Cases.M4N930
import DR.Certificates.FiniteK3Cases.M4N931
import DR.Certificates.FiniteK3Cases.M4N932
import DR.Certificates.FiniteK3Cases.M4N933
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N918To933

theorem exists_valid (n : Nat) (hlo : 918≤n) (hhi : n≤933) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N918.coeff,FiniteK3Cases.C4N918.valid⟩
  · exact ⟨FiniteK3Cases.C4N919.coeff,FiniteK3Cases.C4N919.valid⟩
  · exact ⟨FiniteK3Cases.C4N920.coeff,FiniteK3Cases.C4N920.valid⟩
  · exact ⟨FiniteK3Cases.C4N921.coeff,FiniteK3Cases.C4N921.valid⟩
  · exact ⟨FiniteK3Cases.C4N922.coeff,FiniteK3Cases.C4N922.valid⟩
  · exact ⟨FiniteK3Cases.C4N923.coeff,FiniteK3Cases.C4N923.valid⟩
  · exact ⟨FiniteK3Cases.C4N924.coeff,FiniteK3Cases.C4N924.valid⟩
  · exact ⟨FiniteK3Cases.C4N925.coeff,FiniteK3Cases.C4N925.valid⟩
  · exact ⟨FiniteK3Cases.C4N926.coeff,FiniteK3Cases.C4N926.valid⟩
  · exact ⟨FiniteK3Cases.C4N927.coeff,FiniteK3Cases.C4N927.valid⟩
  · exact ⟨FiniteK3Cases.C4N928.coeff,FiniteK3Cases.C4N928.valid⟩
  · exact ⟨FiniteK3Cases.C4N929.coeff,FiniteK3Cases.C4N929.valid⟩
  · exact ⟨FiniteK3Cases.C4N930.coeff,FiniteK3Cases.C4N930.valid⟩
  · exact ⟨FiniteK3Cases.C4N931.coeff,FiniteK3Cases.C4N931.valid⟩
  · exact ⟨FiniteK3Cases.C4N932.coeff,FiniteK3Cases.C4N932.valid⟩
  · exact ⟨FiniteK3Cases.C4N933.coeff,FiniteK3Cases.C4N933.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N918To933
