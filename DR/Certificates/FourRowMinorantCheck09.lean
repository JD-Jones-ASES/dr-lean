import DR.Certificates.FourRowMinorantData

/-! Kernel checks of every (j,k) coefficient with first index 9. -/
namespace DittertRybin.Certificates.FourRowMinorant
set_option maxRecDepth 10000
set_option maxHeartbeats 0

theorem compactBernsteinNumerator_row_9 : ∀ j k : Fin 35,
    0 ≤ compactBernsteinNumerator 9 j k := by decide +kernel

theorem compactBernsteinNumerator_margin_row_9 : ∀ j k : Fin 35,
    (9 = (0:Fin 35) ∧ j = 0 ∧ k = 0) ∨
      6323724 ≤ compactBernsteinNumerator 9 j k := by decide +kernel

end DittertRybin.Certificates.FourRowMinorant
