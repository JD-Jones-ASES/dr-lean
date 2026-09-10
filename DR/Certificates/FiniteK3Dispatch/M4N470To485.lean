import DR.Certificates.FiniteK3Cases.M4N470
import DR.Certificates.FiniteK3Cases.M4N471
import DR.Certificates.FiniteK3Cases.M4N472
import DR.Certificates.FiniteK3Cases.M4N473
import DR.Certificates.FiniteK3Cases.M4N474
import DR.Certificates.FiniteK3Cases.M4N475
import DR.Certificates.FiniteK3Cases.M4N476
import DR.Certificates.FiniteK3Cases.M4N477
import DR.Certificates.FiniteK3Cases.M4N478
import DR.Certificates.FiniteK3Cases.M4N479
import DR.Certificates.FiniteK3Cases.M4N480
import DR.Certificates.FiniteK3Cases.M4N481
import DR.Certificates.FiniteK3Cases.M4N482
import DR.Certificates.FiniteK3Cases.M4N483
import DR.Certificates.FiniteK3Cases.M4N484
import DR.Certificates.FiniteK3Cases.M4N485
import Mathlib.Tactic.IntervalCases

/-! Bounded exact coverage: each branch carries its actual rational certificate. -/
namespace DittertRybin.Certificates.FiniteK3Dispatch.C4N470To485

theorem exists_valid (n : Nat) (hlo : 470≤n) (hhi : n≤485) :
    ∃ coeff : Fin 93 → ℚ,FiniteK3EnvelopeValid 4 n (by decide) coeff := by
  interval_cases n
  · exact ⟨FiniteK3Cases.C4N470.coeff,FiniteK3Cases.C4N470.valid⟩
  · exact ⟨FiniteK3Cases.C4N471.coeff,FiniteK3Cases.C4N471.valid⟩
  · exact ⟨FiniteK3Cases.C4N472.coeff,FiniteK3Cases.C4N472.valid⟩
  · exact ⟨FiniteK3Cases.C4N473.coeff,FiniteK3Cases.C4N473.valid⟩
  · exact ⟨FiniteK3Cases.C4N474.coeff,FiniteK3Cases.C4N474.valid⟩
  · exact ⟨FiniteK3Cases.C4N475.coeff,FiniteK3Cases.C4N475.valid⟩
  · exact ⟨FiniteK3Cases.C4N476.coeff,FiniteK3Cases.C4N476.valid⟩
  · exact ⟨FiniteK3Cases.C4N477.coeff,FiniteK3Cases.C4N477.valid⟩
  · exact ⟨FiniteK3Cases.C4N478.coeff,FiniteK3Cases.C4N478.valid⟩
  · exact ⟨FiniteK3Cases.C4N479.coeff,FiniteK3Cases.C4N479.valid⟩
  · exact ⟨FiniteK3Cases.C4N480.coeff,FiniteK3Cases.C4N480.valid⟩
  · exact ⟨FiniteK3Cases.C4N481.coeff,FiniteK3Cases.C4N481.valid⟩
  · exact ⟨FiniteK3Cases.C4N482.coeff,FiniteK3Cases.C4N482.valid⟩
  · exact ⟨FiniteK3Cases.C4N483.coeff,FiniteK3Cases.C4N483.valid⟩
  · exact ⟨FiniteK3Cases.C4N484.coeff,FiniteK3Cases.C4N484.valid⟩
  · exact ⟨FiniteK3Cases.C4N485.coeff,FiniteK3Cases.C4N485.valid⟩

end DittertRybin.Certificates.FiniteK3Dispatch.C4N470To485
