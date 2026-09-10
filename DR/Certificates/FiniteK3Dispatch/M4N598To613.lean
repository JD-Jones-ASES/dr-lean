import DR.Certificates.FiniteK3Cases.M4N598
import DR.Certificates.FiniteK3Cases.M4N599
import DR.Certificates.FiniteK3Cases.M4N600
import DR.Certificates.FiniteK3Cases.M4N601
import DR.Certificates.FiniteK3Cases.M4N602
import DR.Certificates.FiniteK3Cases.M4N603
import DR.Certificates.FiniteK3Cases.M4N604
import DR.Certificates.FiniteK3Cases.M4N605
import DR.Certificates.FiniteK3Cases.M4N606
import DR.Certificates.FiniteK3Cases.M4N607
import DR.Certificates.FiniteK3Cases.M4N608
import DR.Certificates.FiniteK3Cases.M4N609
import DR.Certificates.FiniteK3Cases.M4N610
import DR.Certificates.FiniteK3Cases.M4N611
import DR.Certificates.FiniteK3Cases.M4N612
import DR.Certificates.FiniteK3Cases.M4N613
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N598To613

theorem exists_valid (n : Nat) (hlo : 598≤n) (hhi : n≤613) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N598.coeff,FiniteK3Cases.C4N598.valid⟩
  · exact ⟨FiniteK3Cases.C4N599.coeff,FiniteK3Cases.C4N599.valid⟩
  · exact ⟨FiniteK3Cases.C4N600.coeff,FiniteK3Cases.C4N600.valid⟩
  · exact ⟨FiniteK3Cases.C4N601.coeff,FiniteK3Cases.C4N601.valid⟩
  · exact ⟨FiniteK3Cases.C4N602.coeff,FiniteK3Cases.C4N602.valid⟩
  · exact ⟨FiniteK3Cases.C4N603.coeff,FiniteK3Cases.C4N603.valid⟩
  · exact ⟨FiniteK3Cases.C4N604.coeff,FiniteK3Cases.C4N604.valid⟩
  · exact ⟨FiniteK3Cases.C4N605.coeff,FiniteK3Cases.C4N605.valid⟩
  · exact ⟨FiniteK3Cases.C4N606.coeff,FiniteK3Cases.C4N606.valid⟩
  · exact ⟨FiniteK3Cases.C4N607.coeff,FiniteK3Cases.C4N607.valid⟩
  · exact ⟨FiniteK3Cases.C4N608.coeff,FiniteK3Cases.C4N608.valid⟩
  · exact ⟨FiniteK3Cases.C4N609.coeff,FiniteK3Cases.C4N609.valid⟩
  · exact ⟨FiniteK3Cases.C4N610.coeff,FiniteK3Cases.C4N610.valid⟩
  · exact ⟨FiniteK3Cases.C4N611.coeff,FiniteK3Cases.C4N611.valid⟩
  · exact ⟨FiniteK3Cases.C4N612.coeff,FiniteK3Cases.C4N612.valid⟩
  · exact ⟨FiniteK3Cases.C4N613.coeff,FiniteK3Cases.C4N613.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N598To613
