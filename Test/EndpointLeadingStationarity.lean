import DR.Endpoint.LeadingMoments
import Mathlib.Tactic.FinCases

namespace DittertRybin.Tests
open scoped BigOperators
open Certificates

private noncomputable def rowLaw : Board 3 1 := fun _ _ => 1
private noncomputable def masses : Fin 3 → ℝ := ![1/2,1/3,1/6]
private theorem masses_pos (i : Fin 3) : 0<masses i := by
  fin_cases i <;> norm_num [masses]
private theorem masses_sum : (∑ i,masses i)=1 := by
  norm_num [masses,Fin.sum_univ_succ]
private theorem law_nonneg (i : Fin 3) (j : Fin 1) : 0≤rowLaw i j := by norm_num [rowLaw]
private theorem law_normalized (i : Fin 3) : rowSum rowLaw i=1 := by simp [rowLaw,rowSum]

-- A single physical column gives equality in the genuine weighted Cauchy estimate.
example : endpointLeadingGauge (endpointRowBoard masses rowLaw)*
    (endpointLeadingGauge (endpointRowBoard masses rowLaw)+2*endpointLeadingMoment masses rowLaw)=1 := by
  have h1 := endpointLeading_weighted_sum_one (by decide) masses rowLaw
    (fun i => (masses_pos i).le) masses_sum law_nonneg law_normalized
  have h2 := endpointLeading_weighted_sum_two (by decide) masses rowLaw
    (fun i => (masses_pos i).le) masses_sum law_nonneg law_normalized
  simp only [Fin.sum_univ_one] at h1 h2
  have hG : endpointLeadingGauge (endpointRowBoard masses rowLaw)=
      endpointLeadingColumnCost (endpointRowBoard masses rowLaw) 0 := by
    simp [endpointLeadingGauge]
  rw [hG] at h2 ⊢
  rw [← h2]
  calc
    _ = (endpointLeadingColumnCost (endpointRowBoard masses rowLaw) 0*endpointLeadingRatio masses rowLaw 0)^2 := by ring
    _ = 1 := by rw [h1]; norm_num

-- Genuine nonstationarity: this positive probability board cannot be a gauge minimum.
example : ¬IsEndpointRowGaugeMinimum masses rowLaw (fun _ => 0) := by
  intro hmin
  have he := hmin.row_gradient_eq (by decide) masses_pos masses_sum law_nonneg law_normalized
    0 (hasDerivAt_const _ 0) 0 1
  have hA : endpointLeadingRowDerivative masses rowLaw 0=
      endpointLeadingRowDerivative masses rowLaw 1 := by
    simp [endpointLeadingRowDerivative,rowLaw]
  rw [hA] at he
  norm_num [masses] at he
  change endpointLeadingMoment masses rowLaw/(1/2)=endpointLeadingMoment masses rowLaw/(1/3) at he
  norm_num [div_div] at he
  have hp := endpointRowBoard_isProbability masses rowLaw (fun i => (masses_pos i).le)
    masses_sum law_nonneg law_normalized
  have hc := endpointLeadingColumnCost_pos (by decide) (endpointRowBoard masses rowLaw) hp 0
    (by norm_num [colSum,endpointRowBoard,rowLaw,masses,Fin.sum_univ_succ])
  have hD : 0<endpointLeadingMoment masses rowLaw := by
    unfold endpointLeadingMoment
    simp only [Fin.sum_univ_one]
    have hT : endpointLeadingColumnCollision rowLaw 0=6 := by
      norm_num [endpointLeadingColumnCollision,rowLaw]
    rw [hT]
    have hscale : endpointLeadingScale masses=1/36 := by
      norm_num [endpointLeadingScale,masses,Fin.prod_univ_succ,Nat.factorial]
    rw [hscale]
    positivity
  linarith

-- The final multiplier identity accepts any differentiable row penalty.
example {m n : ℕ} (hm : 3≤m) (r : Fin m → ℝ) (X : Board m n) (psi : ℝ → ℝ)
    (hmin : IsEndpointRowGaugeMinimum r X psi) (hr : ∀ i,0<r i) (hs : ∑ i,r i=1)
    (hX : ∀ i j,0≤X i j) (hXS : ∀ i,rowSum X i=1) (tau : ℝ)
    (hpsi : HasDerivAt psi tau (∑ i,r i^2)) (i : Fin m) :
    endpointLeadingRowDerivative r X i=
      endpointLeadingGauge (endpointRowBoard r X)-((m:ℝ)-2)*endpointLeadingMoment r X+
      2*tau*(r i-∑ a,r a^2)+endpointLeadingMoment r X/r i :=
  hmin.stationarity hm hr hs hX hXS tau hpsi i

-- Vanishing columns contribute exactly zero to the full gauge derivative.
example (r w : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => endpointLeadingColumnCost
      (endpointRowBoard (fun i => r i+t*w i) (!![1,0;1,0;1,0] : Board 3 2)) 1) 0 0 := by
  have hfun : (fun t : ℝ => endpointLeadingColumnCost
      (endpointRowBoard (fun i => r i+t*w i) (!![1,0;1,0;1,0] : Board 3 2)) 1)=fun _ => 0 := by
    funext t
    apply endpointLeadingColumnCost_zero_column
    intro i
    fin_cases i <;> norm_num
  rw [hfun]
  exact hasDerivAt_const 0 0

#print axioms hasDerivAt_endpointLeadingColumnCost_full
#print axioms hasDerivAt_endpointLeadingGauge_line
#print axioms IsEndpointRowGaugeMinimum.line_localMin
#print axioms IsEndpointRowGaugeMinimum.gradient_dot_zero
#print axioms IsEndpointRowGaugeMinimum.row_gradient_eq
#print axioms endpointLeading_cost_mul_ratio
#print axioms endpointLeading_column_moment
#print axioms endpointLeading_weighted_sum_one
#print axioms endpointLeading_weighted_sum_two
#print axioms endpointLeading_weighted_cauchy
#print axioms endpointLeading_rowDerivative_sum
#print axioms IsEndpointRowGaugeMinimum.stationarity

end DittertRybin.Tests
