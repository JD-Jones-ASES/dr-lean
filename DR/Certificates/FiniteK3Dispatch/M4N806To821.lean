import DR.Certificates.FiniteK3Cases.M4N806
import DR.Certificates.FiniteK3Cases.M4N807
import DR.Certificates.FiniteK3Cases.M4N808
import DR.Certificates.FiniteK3Cases.M4N809
import DR.Certificates.FiniteK3Cases.M4N810
import DR.Certificates.FiniteK3Cases.M4N811
import DR.Certificates.FiniteK3Cases.M4N812
import DR.Certificates.FiniteK3Cases.M4N813
import DR.Certificates.FiniteK3Cases.M4N814
import DR.Certificates.FiniteK3Cases.M4N815
import DR.Certificates.FiniteK3Cases.M4N816
import DR.Certificates.FiniteK3Cases.M4N817
import DR.Certificates.FiniteK3Cases.M4N818
import DR.Certificates.FiniteK3Cases.M4N819
import DR.Certificates.FiniteK3Cases.M4N820
import DR.Certificates.FiniteK3Cases.M4N821
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N806To821

theorem exists_valid (n : Nat) (hlo : 806≤n) (hhi : n≤821) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N806.coeff,FiniteK3Cases.C4N806.valid⟩
  · exact ⟨FiniteK3Cases.C4N807.coeff,FiniteK3Cases.C4N807.valid⟩
  · exact ⟨FiniteK3Cases.C4N808.coeff,FiniteK3Cases.C4N808.valid⟩
  · exact ⟨FiniteK3Cases.C4N809.coeff,FiniteK3Cases.C4N809.valid⟩
  · exact ⟨FiniteK3Cases.C4N810.coeff,FiniteK3Cases.C4N810.valid⟩
  · exact ⟨FiniteK3Cases.C4N811.coeff,FiniteK3Cases.C4N811.valid⟩
  · exact ⟨FiniteK3Cases.C4N812.coeff,FiniteK3Cases.C4N812.valid⟩
  · exact ⟨FiniteK3Cases.C4N813.coeff,FiniteK3Cases.C4N813.valid⟩
  · exact ⟨FiniteK3Cases.C4N814.coeff,FiniteK3Cases.C4N814.valid⟩
  · exact ⟨FiniteK3Cases.C4N815.coeff,FiniteK3Cases.C4N815.valid⟩
  · exact ⟨FiniteK3Cases.C4N816.coeff,FiniteK3Cases.C4N816.valid⟩
  · exact ⟨FiniteK3Cases.C4N817.coeff,FiniteK3Cases.C4N817.valid⟩
  · exact ⟨FiniteK3Cases.C4N818.coeff,FiniteK3Cases.C4N818.valid⟩
  · exact ⟨FiniteK3Cases.C4N819.coeff,FiniteK3Cases.C4N819.valid⟩
  · exact ⟨FiniteK3Cases.C4N820.coeff,FiniteK3Cases.C4N820.valid⟩
  · exact ⟨FiniteK3Cases.C4N821.coeff,FiniteK3Cases.C4N821.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N806To821
