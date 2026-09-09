import DR.Square.SpectralFiveSetup

/-! Exact unit-box coordinates of the actual minimum-row/maximum-column pair. -/

namespace DittertRybin
open Certificates.SpectralFiveSingleton

theorem five_globalMax_singleton_coordinates (A : Board 5 5)
    (hA : ∀ i j, 0 ≤ A i j) (hmass : totalMass A = 5)
    (hmax : ∀ B : Board 5 5, (∀ i j, 0 ≤ B i j) → totalMass B = 5 →
      dittertFunctional B ≤ dittertFunctional A)
    (i j : Fin 5) (hrow : ∀ r, rowSum A i ≤ rowSum A r)
    (hcol : ∀ c, colSum A c ≤ colSum A j) :
    let t := fiveDeficitParameter (dittertConstant 5-A.permanent)
    ∃ x y : ℝ, (0 ≤ x ∧ x ≤ 1) ∧ (0 ≤ y ∧ y ≤ 1) ∧
      rowSum A i = 1-(23/50)*t*x ∧ colSum A j = 1+(1/2)*t*y := by
  dsimp only
  obtain ⟨ha,hb⟩ := five_extremal_marginals_straddle_one A hmass i j hrow hcol
  obtain ⟨hr,hc⟩ := five_globalMax_marginal_bounds A hA hmass hmax
  have hu : 0 ≤ 1-rowSum A i := by linarith
  have hu1 : 1-rowSum A i ≤ (23/50)*fiveDeficitParameter (dittertConstant 5-A.permanent) :=
    by linarith [(hr i).1]
  have hv : 0 ≤ colSum A j-1 := by linarith
  have hv1 : colSum A j-1 ≤ fiveDeficitParameter (dittertConstant 5-A.permanent)/2 :=
    by linarith [(hc j).2]
  obtain ⟨x,y,hx,hy,huEq,hvEq⟩ := singleton_unit_coordinates
    (fiveDeficitParameter_nonneg _) hu hu1 hv hv1
  exact ⟨x,y,hx,hy,by linarith,by linarith⟩

end DittertRybin
