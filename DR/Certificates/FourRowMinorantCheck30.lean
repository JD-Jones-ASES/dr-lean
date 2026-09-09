import DR.Certificates.FourRowMinorantData

/-! Kernel checks of every (j,k) coefficient with first index 30. -/
namespace DittertRybin.Certificates.FourRowMinorant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem compactBernsteinNumerator_row_30 : ∀ j k : Fin 35,
    0 ≤ compactBernsteinNumerator 30 j k := by decide +kernel

theorem compactBernsteinNumerator_margin_row_30 : ∀ j k : Fin 35,
    (30 = (0:Fin 35) ∧ j = 0 ∧ k = 0) ∨
      6323724 ≤ compactBernsteinNumerator 30 j k := by decide +kernel

end DittertRybin.Certificates.FourRowMinorant
